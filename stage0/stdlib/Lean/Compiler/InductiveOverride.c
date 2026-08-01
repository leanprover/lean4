// Lean compiler output
// Module: Lean.Compiler.InductiveOverride
// Imports: public import Lean.ProjFns public import Lean.Structure public import Lean.Meta.CasesInfo
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
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_isSparseCasesOn(lean_object*, lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_getForallBody(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_getForallArity(lean_object*);
lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantVal(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* l_Lean_getCasesInfo(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_instInhabitedInductiveOverrideInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_instInhabitedInductiveOverrideInfo_default___closed__0 = (const lean_object*)&l_Lean_Compiler_instInhabitedInductiveOverrideInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_instInhabitedInductiveOverrideInfo_default = (const lean_object*)&l_Lean_Compiler_instInhabitedInductiveOverrideInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_instInhabitedInductiveOverrideInfo = (const lean_object*)&l_Lean_Compiler_instInhabitedInductiveOverrideInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_instInhabitedCtorOverrideInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_instInhabitedCtorOverrideInfo_default___closed__0 = (const lean_object*)&l_Lean_Compiler_instInhabitedCtorOverrideInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_instInhabitedCtorOverrideInfo_default = (const lean_object*)&l_Lean_Compiler_instInhabitedCtorOverrideInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_instInhabitedCtorOverrideInfo = (const lean_object*)&l_Lean_Compiler_instInhabitedCtorOverrideInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_simpleType_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_simpleType_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_inductiveType_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_inductiveType_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_constructor_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_constructor_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_isCases_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_isCases_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_projFn_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_projFn_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__0 = (const lean_object*)&l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__1 = (const lean_object*)&l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__2;
static lean_once_cell_t l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_instInhabitedInductiveOverride_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_instInhabitedInductiveOverride;
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_name___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__3_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__3_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__4_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__5_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__5_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__6_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__6_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__3_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__4_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "inductiveOverrideExt"};
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 200, 217, 74, 194, 95, 151, 232)}};
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__5_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__6_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_inductiveOverrideExt;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_addInductiveOverride_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_addInductiveOverride_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_addInductiveOverride___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "`, it is not defined in the current module but in `"};
static const lean_object* l_Lean_Compiler_addInductiveOverride___closed__0 = (const lean_object*)&l_Lean_Compiler_addInductiveOverride___closed__0_value;
static const lean_string_object l_Lean_Compiler_addInductiveOverride___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Compiler_addInductiveOverride___closed__1 = (const lean_object*)&l_Lean_Compiler_addInductiveOverride___closed__1_value;
static const lean_string_object l_Lean_Compiler_addInductiveOverride___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Compiler.InductiveOverride"};
static const lean_object* l_Lean_Compiler_addInductiveOverride___closed__2 = (const lean_object*)&l_Lean_Compiler_addInductiveOverride___closed__2_value;
static const lean_string_object l_Lean_Compiler_addInductiveOverride___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Compiler.addInductiveOverride"};
static const lean_object* l_Lean_Compiler_addInductiveOverride___closed__3 = (const lean_object*)&l_Lean_Compiler_addInductiveOverride___closed__3_value;
static const lean_string_object l_Lean_Compiler_addInductiveOverride___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "cannot add an inductive override for `"};
static const lean_object* l_Lean_Compiler_addInductiveOverride___closed__4 = (const lean_object*)&l_Lean_Compiler_addInductiveOverride___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_addInductiveOverride(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_getInductiveOverride_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_getInductiveOverride_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getInductiveOverride_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_getInductiveOverride_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_getInductiveOverride_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Compiler_hasInductiveOverride_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_hasInductiveOverride_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_hasInductiveOverride(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasInductiveOverride___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Compiler_hasInductiveOverride_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_hasInductiveOverride_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Compiler.InductiveOverride.0.Lean.Compiler.casesEliminatorInduct"};
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__0 = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__1 = (const lean_object*)&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getCasesInfoOverride_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getCasesInfoOverride_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_isCasesOnLikeOverride(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isCasesOnLikeOverride___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getProjectionFnInfoOverride_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_isProjectionFnOverride(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isProjectionFnOverride___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isCtorOverrideSimple_x3f(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___closed__0_value;
static const lean_string_object l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isCtorOverride_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isCtorOverride_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_getConstInfoCtorOverride___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "` is not a constructor to the compiler"};
static const lean_object* l_Lean_Compiler_getConstInfoCtorOverride___closed__0 = (const lean_object*)&l_Lean_Compiler_getConstInfoCtorOverride___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_getConstInfoCtorOverride___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_getConstInfoCtorOverride___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_getConstInfoCtorOverride(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getConstInfoCtorOverride___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverrideSimpleCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverride___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverride___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverride(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverride___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverrideSimple_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverrideSimple_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverrideSimple_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverrideSimple_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Compiler_isCompilerRelevantType_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Compiler_isCompilerRelevantType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Compiler_isCompilerRelevantType_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Compiler_isCompilerRelevantType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isCompilerRelevantType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isCompilerRelevantType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_panic___at___00Lean_Compiler_hasNoncomputableOverride_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_hasNoncomputableOverride_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_Compiler_hasNoncomputableOverride___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Compiler.hasNoncomputableOverride"};
static const lean_object* l_Lean_Compiler_hasNoncomputableOverride___closed__0 = (const lean_object*)&l_Lean_Compiler_hasNoncomputableOverride___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_hasNoncomputableOverride___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_hasNoncomputableOverride___closed__1;
LEAN_EXPORT uint8_t l_Lean_Compiler_hasNoncomputableOverride(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasNoncomputableOverride___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_ctorIdx(lean_object* v_x_12_){
_start:
{
switch(lean_obj_tag(v_x_12_))
{
case 0:
{
lean_object* v___x_13_; 
v___x_13_ = lean_unsigned_to_nat(0u);
return v___x_13_;
}
case 1:
{
lean_object* v___x_14_; 
v___x_14_ = lean_unsigned_to_nat(1u);
return v___x_14_;
}
case 2:
{
lean_object* v___x_15_; 
v___x_15_ = lean_unsigned_to_nat(2u);
return v___x_15_;
}
case 3:
{
lean_object* v___x_16_; 
v___x_16_ = lean_unsigned_to_nat(3u);
return v___x_16_;
}
default: 
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(4u);
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_ctorIdx___boxed(lean_object* v_x_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_Compiler_InductiveOverride_ctorIdx(v_x_18_);
lean_dec_ref(v_x_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_ctorElim___redArg(lean_object* v_t_20_, lean_object* v_k_21_){
_start:
{
if (lean_obj_tag(v_t_20_) == 3)
{
lean_object* v_elimName_22_; lean_object* v___x_23_; 
v_elimName_22_ = lean_ctor_get(v_t_20_, 0);
lean_inc(v_elimName_22_);
lean_dec_ref_known(v_t_20_, 1);
v___x_23_ = lean_apply_1(v_k_21_, v_elimName_22_);
return v___x_23_;
}
else
{
lean_object* v_typeName_24_; lean_object* v_impureType_25_; lean_object* v___x_26_; 
v_typeName_24_ = lean_ctor_get(v_t_20_, 0);
lean_inc(v_typeName_24_);
v_impureType_25_ = lean_ctor_get(v_t_20_, 1);
lean_inc_ref(v_impureType_25_);
lean_dec_ref(v_t_20_);
v___x_26_ = lean_apply_2(v_k_21_, v_typeName_24_, v_impureType_25_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_ctorElim(lean_object* v_motive_27_, lean_object* v_ctorIdx_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_k_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Compiler_InductiveOverride_ctorElim___redArg(v_t_29_, v_k_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_ctorElim___boxed(lean_object* v_motive_33_, lean_object* v_ctorIdx_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_k_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Compiler_InductiveOverride_ctorElim(v_motive_33_, v_ctorIdx_34_, v_t_35_, v_h_36_, v_k_37_);
lean_dec(v_ctorIdx_34_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_simpleType_elim___redArg(lean_object* v_t_39_, lean_object* v_simpleType_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Compiler_InductiveOverride_ctorElim___redArg(v_t_39_, v_simpleType_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_simpleType_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_simpleType_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Compiler_InductiveOverride_ctorElim___redArg(v_t_43_, v_simpleType_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_inductiveType_elim___redArg(lean_object* v_t_47_, lean_object* v_inductiveType_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Compiler_InductiveOverride_ctorElim___redArg(v_t_47_, v_inductiveType_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_inductiveType_elim(lean_object* v_motive_50_, lean_object* v_t_51_, lean_object* v_h_52_, lean_object* v_inductiveType_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_Compiler_InductiveOverride_ctorElim___redArg(v_t_51_, v_inductiveType_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_constructor_elim___redArg(lean_object* v_t_55_, lean_object* v_constructor_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Compiler_InductiveOverride_ctorElim___redArg(v_t_55_, v_constructor_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_constructor_elim(lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_constructor_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Compiler_InductiveOverride_ctorElim___redArg(v_t_59_, v_constructor_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_isCases_elim___redArg(lean_object* v_t_63_, lean_object* v_isCases_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Compiler_InductiveOverride_ctorElim___redArg(v_t_63_, v_isCases_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_isCases_elim(lean_object* v_motive_66_, lean_object* v_t_67_, lean_object* v_h_68_, lean_object* v_isCases_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Compiler_InductiveOverride_ctorElim___redArg(v_t_67_, v_isCases_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_projFn_elim___redArg(lean_object* v_t_71_, lean_object* v_projFn_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Compiler_InductiveOverride_ctorElim___redArg(v_t_71_, v_projFn_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_projFn_elim(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_projFn_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Compiler_InductiveOverride_ctorElim___redArg(v_t_75_, v_projFn_77_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__2(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_box(0);
v___x_83_ = ((lean_object*)(l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__1));
v___x_84_ = l_Lean_Expr_const___override(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__3(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_obj_once(&l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__2, &l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__2_once, _init_l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__2);
v___x_86_ = lean_box(0);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Compiler_instInhabitedInductiveOverride_default(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_obj_once(&l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__3, &l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__3_once, _init_l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__3);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Compiler_instInhabitedInductiveOverride(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Compiler_instInhabitedInductiveOverride_default;
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_name(lean_object* v_x_90_){
_start:
{
lean_object* v_typeName_91_; 
v_typeName_91_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_typeName_91_);
return v_typeName_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InductiveOverride_name___boxed(lean_object* v_x_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Compiler_InductiveOverride_name(v_x_92_);
lean_dec_ref(v_x_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(lean_object* v_map_94_, lean_object* v_x_95_){
_start:
{
lean_object* v_typeName_96_; lean_object* v___x_97_; 
v_typeName_96_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_typeName_96_);
v___x_97_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_typeName_96_, v_x_95_, v_map_94_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_98_, lean_object* v_x_99_){
_start:
{
if (lean_obj_tag(v_x_99_) == 0)
{
lean_object* v_v_100_; lean_object* v_l_101_; lean_object* v_r_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_v_100_ = lean_ctor_get(v_x_99_, 2);
lean_inc(v_v_100_);
v_l_101_ = lean_ctor_get(v_x_99_, 3);
lean_inc(v_l_101_);
v_r_102_ = lean_ctor_get(v_x_99_, 4);
lean_inc(v_r_102_);
lean_dec_ref_known(v_x_99_, 5);
v___x_103_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__0_spec__0(v_init_98_, v_l_101_);
v___x_104_ = lean_array_push(v___x_103_, v_v_100_);
v_init_98_ = v___x_104_;
v_x_99_ = v_r_102_;
goto _start;
}
else
{
return v_init_98_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_106_, lean_object* v_pivot_107_, lean_object* v_as_108_, lean_object* v_i_109_, lean_object* v_k_110_){
_start:
{
uint8_t v___y_112_; lean_object* v___y_122_; uint8_t v___x_125_; 
v___x_125_ = lean_nat_dec_lt(v_k_110_, v_hi_106_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec(v_k_110_);
v___x_126_ = lean_array_fswap(v_as_108_, v_i_109_, v_hi_106_);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v_i_109_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
return v___x_127_;
}
else
{
lean_object* v___x_128_; lean_object* v_typeName_129_; 
v___x_128_ = lean_array_fget_borrowed(v_as_108_, v_k_110_);
v_typeName_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_typeName_129_);
v___y_122_ = v_typeName_129_;
goto v___jp_121_;
}
v___jp_111_:
{
if (v___y_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_114_ = lean_nat_add(v_k_110_, v___x_113_);
lean_dec(v_k_110_);
v_k_110_ = v___x_114_;
goto _start;
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_116_ = lean_array_fswap(v_as_108_, v_i_109_, v_k_110_);
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_add(v_i_109_, v___x_117_);
lean_dec(v_i_109_);
v___x_119_ = lean_nat_add(v_k_110_, v___x_117_);
lean_dec(v_k_110_);
v_as_108_ = v___x_116_;
v_i_109_ = v___x_118_;
v_k_110_ = v___x_119_;
goto _start;
}
}
v___jp_121_:
{
lean_object* v_typeName_123_; uint8_t v___x_124_; 
v_typeName_123_ = lean_ctor_get(v_pivot_107_, 0);
v___x_124_ = l_Lean_Name_quickLt(v___y_122_, v_typeName_123_);
lean_dec(v___y_122_);
v___y_112_ = v___x_124_;
goto v___jp_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_130_, lean_object* v_pivot_131_, lean_object* v_as_132_, lean_object* v_i_133_, lean_object* v_k_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_130_, v_pivot_131_, v_as_132_, v_i_133_, v_k_134_);
lean_dec_ref(v_pivot_131_);
lean_dec(v_hi_130_);
return v_res_135_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_a_136_, lean_object* v_b_137_){
_start:
{
lean_object* v___y_139_; lean_object* v_typeName_142_; 
v_typeName_142_ = lean_ctor_get(v_a_136_, 0);
v___y_139_ = v_typeName_142_;
goto v___jp_138_;
v___jp_138_:
{
lean_object* v_typeName_140_; uint8_t v___x_141_; 
v_typeName_140_ = lean_ctor_get(v_b_137_, 0);
v___x_141_ = l_Lean_Name_quickLt(v___y_139_, v_typeName_140_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_a_143_, lean_object* v_b_144_){
_start:
{
uint8_t v_res_145_; lean_object* v_r_146_; 
v_res_145_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_143_, v_b_144_);
lean_dec_ref(v_b_144_);
lean_dec_ref(v_a_143_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_147_, lean_object* v_as_148_, lean_object* v_lo_149_, lean_object* v_hi_150_){
_start:
{
lean_object* v___y_152_; uint8_t v___x_162_; 
v___x_162_ = lean_nat_dec_lt(v_lo_149_, v_hi_150_);
if (v___x_162_ == 0)
{
lean_dec(v_lo_149_);
return v_as_148_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v_mid_165_; lean_object* v___y_167_; lean_object* v___y_173_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_163_ = lean_nat_add(v_lo_149_, v_hi_150_);
v___x_164_ = lean_unsigned_to_nat(1u);
v_mid_165_ = lean_nat_shiftr(v___x_163_, v___x_164_);
lean_dec(v___x_163_);
v___x_178_ = lean_array_fget_borrowed(v_as_148_, v_mid_165_);
v___x_179_ = lean_array_fget_borrowed(v_as_148_, v_lo_149_);
v___x_180_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
v___y_173_ = v_as_148_;
goto v___jp_172_;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = lean_array_fswap(v_as_148_, v_lo_149_, v_mid_165_);
v___y_173_ = v___x_181_;
goto v___jp_172_;
}
v___jp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_168_ = lean_array_fget_borrowed(v___y_167_, v_mid_165_);
v___x_169_ = lean_array_fget_borrowed(v___y_167_, v_hi_150_);
v___x_170_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_168_, v___x_169_);
if (v___x_170_ == 0)
{
lean_dec(v_mid_165_);
v___y_152_ = v___y_167_;
goto v___jp_151_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = lean_array_fswap(v___y_167_, v_mid_165_, v_hi_150_);
lean_dec(v_mid_165_);
v___y_152_ = v___x_171_;
goto v___jp_151_;
}
}
v___jp_172_:
{
lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_174_ = lean_array_fget_borrowed(v___y_173_, v_hi_150_);
v___x_175_ = lean_array_fget_borrowed(v___y_173_, v_lo_149_);
v___x_176_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_174_, v___x_175_);
if (v___x_176_ == 0)
{
v___y_167_ = v___y_173_;
goto v___jp_166_;
}
else
{
lean_object* v___x_177_; 
v___x_177_ = lean_array_fswap(v___y_173_, v_lo_149_, v_hi_150_);
v___y_167_ = v___x_177_;
goto v___jp_166_;
}
}
}
v___jp_151_:
{
lean_object* v_pivot_153_; lean_object* v___x_154_; lean_object* v_fst_155_; lean_object* v_snd_156_; uint8_t v___x_157_; 
v_pivot_153_ = lean_array_fget(v___y_152_, v_hi_150_);
lean_inc_n(v_lo_149_, 2);
v___x_154_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_150_, v_pivot_153_, v___y_152_, v_lo_149_, v_lo_149_);
lean_dec(v_pivot_153_);
v_fst_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_fst_155_);
v_snd_156_ = lean_ctor_get(v___x_154_, 1);
lean_inc(v_snd_156_);
lean_dec_ref(v___x_154_);
v___x_157_ = lean_nat_dec_le(v_hi_150_, v_fst_155_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg(v_n_147_, v_snd_156_, v_lo_149_, v_fst_155_);
v___x_159_ = lean_unsigned_to_nat(1u);
v___x_160_ = lean_nat_add(v_fst_155_, v___x_159_);
lean_dec(v_fst_155_);
v_as_148_ = v___x_158_;
v_lo_149_ = v___x_160_;
goto _start;
}
else
{
lean_dec(v_fst_155_);
lean_dec(v_lo_149_);
return v_snd_156_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_182_, lean_object* v_as_183_, lean_object* v_lo_184_, lean_object* v_hi_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg(v_n_182_, v_as_183_, v_lo_184_, v_hi_185_);
lean_dec(v_hi_185_);
lean_dec(v_n_182_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(lean_object* v_x_187_, lean_object* v_s_188_){
_start:
{
lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_197_; lean_object* v___y_198_; lean_object* v___y_199_; lean_object* v___y_200_; lean_object* v___y_203_; 
if (lean_obj_tag(v_s_188_) == 0)
{
lean_object* v_size_213_; 
v_size_213_ = lean_ctor_get(v_s_188_, 0);
lean_inc(v_size_213_);
v___y_203_ = v_size_213_;
goto v___jp_202_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = lean_unsigned_to_nat(0u);
v___y_203_ = v___x_214_;
goto v___jp_202_;
}
v___jp_189_:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg(v___y_191_, v___y_190_, v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec(v___y_191_);
lean_inc_ref_n(v___x_194_, 2);
v___x_195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
lean_ctor_set(v___x_195_, 2, v___x_194_);
return v___x_195_;
}
v___jp_196_:
{
uint8_t v___x_201_; 
v___x_201_ = lean_nat_dec_le(v___y_200_, v___y_197_);
if (v___x_201_ == 0)
{
lean_dec(v___y_197_);
lean_inc(v___y_200_);
v___y_190_ = v___y_198_;
v___y_191_ = v___y_199_;
v___y_192_ = v___y_200_;
v___y_193_ = v___y_200_;
goto v___jp_189_;
}
else
{
v___y_190_ = v___y_198_;
v___y_191_ = v___y_199_;
v___y_192_ = v___y_200_;
v___y_193_ = v___y_197_;
goto v___jp_189_;
}
}
v___jp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_204_ = lean_mk_empty_array_with_capacity(v___y_203_);
lean_dec(v___y_203_);
v___x_205_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__0_spec__0(v___x_204_, v_s_188_);
v___x_206_ = lean_array_get_size(v___x_205_);
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_nat_dec_eq(v___x_206_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_nat_sub(v___x_206_, v___x_209_);
v___x_211_ = lean_nat_dec_le(v___x_207_, v___x_210_);
if (v___x_211_ == 0)
{
lean_inc(v___x_210_);
v___y_197_ = v___x_210_;
v___y_198_ = v___x_205_;
v___y_199_ = v___x_206_;
v___y_200_ = v___x_210_;
goto v___jp_196_;
}
else
{
v___y_197_ = v___x_210_;
v___y_198_ = v___x_205_;
v___y_199_ = v___x_206_;
v___y_200_ = v___x_207_;
goto v___jp_196_;
}
}
else
{
lean_object* v___x_212_; 
lean_inc_ref_n(v___x_205_, 2);
v___x_212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_212_, 0, v___x_205_);
lean_ctor_set(v___x_212_, 1, v___x_205_);
lean_ctor_set(v___x_212_, 2, v___x_205_);
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed(lean_object* v_x_215_, lean_object* v_s_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(v_x_215_, v_s_216_);
lean_dec_ref(v_x_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(lean_object* v_x_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = lean_box(0);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed(lean_object* v_x_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(v_x_220_);
lean_dec(v_x_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__2(lean_object* v_newState_222_, lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_224_) == 0)
{
return v_x_223_;
}
else
{
lean_object* v_head_225_; lean_object* v_tail_226_; lean_object* v___x_227_; 
v_head_225_ = lean_ctor_get(v_x_224_, 0);
lean_inc(v_head_225_);
v_tail_226_ = lean_ctor_get(v_x_224_, 1);
lean_inc(v_tail_226_);
lean_dec_ref_known(v_x_224_, 2);
v___x_227_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_222_, v_head_225_);
if (lean_obj_tag(v___x_227_) == 1)
{
lean_object* v_val_228_; lean_object* v___x_229_; 
v_val_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v___x_227_, 1);
v___x_229_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_225_, v_val_228_, v_x_223_);
v_x_223_ = v___x_229_;
v_x_224_ = v_tail_226_;
goto _start;
}
else
{
lean_dec(v___x_227_);
lean_dec(v_head_225_);
v_x_224_ = v_tail_226_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__2___boxed(lean_object* v_newState_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_List_foldl___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__2(v_newState_232_, v_x_233_, v_x_234_);
lean_dec(v_newState_232_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__3_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(lean_object* v_x_236_, lean_object* v_newState_237_, lean_object* v_newConsts_238_, lean_object* v_s_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_List_foldl___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__2(v_newState_237_, v_s_239_, v_newConsts_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__3_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed(lean_object* v_x_241_, lean_object* v_newState_242_, lean_object* v_newConsts_243_, lean_object* v_s_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__3_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(v_x_241_, v_newState_242_, v_newConsts_243_, v_s_244_);
lean_dec(v_newState_242_);
lean_dec(v_x_241_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__4_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(lean_object* v_map_246_){
_start:
{
lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_256_; 
if (lean_obj_tag(v_map_246_) == 0)
{
lean_object* v_size_265_; 
v_size_265_ = lean_ctor_get(v_map_246_, 0);
lean_inc(v_size_265_);
v___y_256_ = v_size_265_;
goto v___jp_255_;
}
else
{
lean_object* v___x_266_; 
v___x_266_ = lean_unsigned_to_nat(0u);
v___y_256_ = v___x_266_;
goto v___jp_255_;
}
v___jp_247_:
{
uint8_t v___x_252_; 
v___x_252_ = lean_nat_dec_le(v___y_251_, v___y_250_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec(v___y_250_);
lean_inc(v___y_251_);
v___x_253_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg(v___y_249_, v___y_248_, v___y_251_, v___y_251_);
lean_dec(v___y_251_);
lean_dec(v___y_249_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; 
v___x_254_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg(v___y_249_, v___y_248_, v___y_251_, v___y_250_);
lean_dec(v___y_250_);
lean_dec(v___y_249_);
return v___x_254_;
}
}
v___jp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_257_ = lean_mk_empty_array_with_capacity(v___y_256_);
lean_dec(v___y_256_);
v___x_258_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__0_spec__0(v___x_257_, v_map_246_);
v___x_259_ = lean_array_get_size(v___x_258_);
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_nat_dec_eq(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = lean_nat_sub(v___x_259_, v___x_262_);
v___x_264_ = lean_nat_dec_le(v___x_260_, v___x_263_);
if (v___x_264_ == 0)
{
lean_inc(v___x_263_);
v___y_248_ = v___x_258_;
v___y_249_ = v___x_259_;
v___y_250_ = v___x_263_;
v___y_251_ = v___x_263_;
goto v___jp_247_;
}
else
{
v___y_248_ = v___x_258_;
v___y_249_ = v___x_259_;
v___y_250_ = v___x_263_;
v___y_251_ = v___x_260_;
goto v___jp_247_;
}
}
else
{
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__5_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(lean_object* v___x_267_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__5_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed(lean_object* v___x_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__5_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(v___x_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__6_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(lean_object* v___x_273_, lean_object* v_x_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_273_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__6_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed(lean_object* v___x_278_, lean_object* v_x_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___lam__6_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(v___x_278_, v_x_279_, v___y_280_);
lean_dec_ref(v___y_280_);
lean_dec_ref(v_x_279_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_));
v___x_315_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2____boxed(lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_();
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__0(lean_object* v_init_318_, lean_object* v_t_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__0_spec__0(v_init_318_, v_t_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1(lean_object* v_n_321_, lean_object* v_as_322_, lean_object* v_lo_323_, lean_object* v_hi_324_, lean_object* v_w_325_, lean_object* v_hlo_326_, lean_object* v_hhi_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg(v_n_321_, v_as_322_, v_lo_323_, v_hi_324_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_329_, lean_object* v_as_330_, lean_object* v_lo_331_, lean_object* v_hi_332_, lean_object* v_w_333_, lean_object* v_hlo_334_, lean_object* v_hhi_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1(v_n_329_, v_as_330_, v_lo_331_, v_hi_332_, v_w_333_, v_hlo_334_, v_hhi_335_);
lean_dec(v_hi_332_);
lean_dec(v_n_329_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_337_, lean_object* v_lo_338_, lean_object* v_hi_339_, lean_object* v_hhi_340_, lean_object* v_pivot_341_, lean_object* v_as_342_, lean_object* v_i_343_, lean_object* v_k_344_, lean_object* v_ilo_345_, lean_object* v_ik_346_, lean_object* v_w_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_339_, v_pivot_341_, v_as_342_, v_i_343_, v_k_344_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_349_, lean_object* v_lo_350_, lean_object* v_hi_351_, lean_object* v_hhi_352_, lean_object* v_pivot_353_, lean_object* v_as_354_, lean_object* v_i_355_, lean_object* v_k_356_, lean_object* v_ilo_357_, lean_object* v_ik_358_, lean_object* v_w_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1_spec__2(v_n_349_, v_lo_350_, v_hi_351_, v_hhi_352_, v_pivot_353_, v_as_354_, v_i_355_, v_k_356_, v_ilo_357_, v_ik_358_, v_w_359_);
lean_dec_ref(v_pivot_353_);
lean_dec(v_hi_351_);
lean_dec(v_lo_350_);
lean_dec(v_n_349_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_addInductiveOverride_spec__0(lean_object* v_env_361_, lean_object* v_msg_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_panic_fn_borrowed(v_env_361_, v_msg_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_addInductiveOverride_spec__0___boxed(lean_object* v_env_364_, lean_object* v_msg_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_panic___at___00Lean_Compiler_addInductiveOverride_spec__0(v_env_364_, v_msg_365_);
lean_dec_ref(v_env_364_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_addInductiveOverride(lean_object* v_env_372_, lean_object* v_override_373_){
_start:
{
lean_object* v___x_374_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_397_; lean_object* v_typeName_411_; 
v___x_374_ = lean_box(0);
v_typeName_411_ = lean_ctor_get(v_override_373_, 0);
lean_inc(v_typeName_411_);
v___y_397_ = v_typeName_411_;
goto v___jp_396_;
v___jp_375_:
{
uint8_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_383_ = 1;
v___x_384_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_382_, v___x_383_);
lean_inc_ref(v___y_379_);
v___x_385_ = lean_string_append(v___y_379_, v___x_384_);
lean_dec_ref(v___x_384_);
v___x_386_ = ((lean_object*)(l_Lean_Compiler_addInductiveOverride___closed__0));
v___x_387_ = lean_string_append(v___x_385_, v___x_386_);
v___x_388_ = l_Lean_Environment_allImportedModuleNames(v_env_372_);
v___x_389_ = lean_array_get(v___x_374_, v___x_388_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___x_388_);
v___x_390_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_389_, v___x_383_);
v___x_391_ = lean_string_append(v___x_387_, v___x_390_);
lean_dec_ref(v___x_390_);
v___x_392_ = ((lean_object*)(l_Lean_Compiler_addInductiveOverride___closed__1));
v___x_393_ = lean_string_append(v___x_391_, v___x_392_);
v___x_394_ = l_mkPanicMessageWithDecl(v___y_378_, v___y_381_, v___y_376_, v___y_377_, v___x_393_);
lean_dec_ref(v___x_393_);
v___x_395_ = lean_panic_fn_borrowed(v_env_372_, v___x_394_);
lean_dec_ref(v_env_372_);
return v___x_395_;
}
v___jp_396_:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_372_, v___y_397_);
lean_dec(v___y_397_);
if (lean_obj_tag(v___x_398_) == 1)
{
lean_object* v_val_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v_typeName_405_; 
v_val_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_val_399_);
lean_dec_ref_known(v___x_398_, 1);
v___x_400_ = ((lean_object*)(l_Lean_Compiler_addInductiveOverride___closed__2));
v___x_401_ = ((lean_object*)(l_Lean_Compiler_addInductiveOverride___closed__3));
v___x_402_ = lean_unsigned_to_nat(94u);
v___x_403_ = lean_unsigned_to_nat(4u);
v___x_404_ = ((lean_object*)(l_Lean_Compiler_addInductiveOverride___closed__4));
v_typeName_405_ = lean_ctor_get(v_override_373_, 0);
lean_inc(v_typeName_405_);
lean_dec_ref(v_override_373_);
v___y_376_ = v___x_402_;
v___y_377_ = v___x_403_;
v___y_378_ = v___x_400_;
v___y_379_ = v___x_404_;
v___y_380_ = v_val_399_;
v___y_381_ = v___x_401_;
v___y_382_ = v_typeName_405_;
goto v___jp_375_;
}
else
{
lean_object* v___x_406_; lean_object* v_toEnvExtension_407_; lean_object* v_asyncMode_408_; lean_object* v_typeName_409_; lean_object* v___x_410_; 
lean_dec(v___x_398_);
v___x_406_ = l_Lean_Compiler_inductiveOverrideExt;
v_toEnvExtension_407_ = lean_ctor_get(v___x_406_, 0);
v_asyncMode_408_ = lean_ctor_get(v_toEnvExtension_407_, 2);
v_typeName_409_ = lean_ctor_get(v_override_373_, 0);
lean_inc(v_typeName_409_);
v___x_410_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_406_, v_env_372_, v_override_373_, v_asyncMode_408_, v_typeName_409_);
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_getInductiveOverride_x3f_spec__0___redArg(lean_object* v_as_412_, lean_object* v_k_413_, lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_m_418_; lean_object* v_a_419_; uint8_t v___x_420_; 
v___x_416_ = lean_nat_add(v_x_414_, v_x_415_);
v___x_417_ = lean_unsigned_to_nat(1u);
v_m_418_ = lean_nat_shiftr(v___x_416_, v___x_417_);
lean_dec(v___x_416_);
v_a_419_ = lean_array_fget_borrowed(v_as_412_, v_m_418_);
v___x_420_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_419_, v_k_413_);
if (v___x_420_ == 0)
{
uint8_t v___x_421_; 
lean_dec(v_x_415_);
v___x_421_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_413_, v_a_419_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
lean_dec(v_m_418_);
lean_dec(v_x_414_);
lean_inc(v_a_419_);
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v_a_419_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_nat_dec_eq(v_m_418_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = lean_nat_sub(v_m_418_, v___x_417_);
lean_dec(v_m_418_);
v___x_426_ = lean_nat_dec_lt(v___x_425_, v_x_414_);
if (v___x_426_ == 0)
{
v_x_415_ = v___x_425_;
goto _start;
}
else
{
lean_object* v___x_428_; 
lean_dec(v___x_425_);
lean_dec(v_x_414_);
v___x_428_ = lean_box(0);
return v___x_428_;
}
}
else
{
lean_object* v___x_429_; 
lean_dec(v_m_418_);
lean_dec(v_x_414_);
v___x_429_ = lean_box(0);
return v___x_429_;
}
}
}
else
{
lean_object* v___x_430_; uint8_t v___x_431_; 
lean_dec(v_x_414_);
v___x_430_ = lean_nat_add(v_m_418_, v___x_417_);
lean_dec(v_m_418_);
v___x_431_ = lean_nat_dec_le(v___x_430_, v_x_415_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
lean_dec(v___x_430_);
lean_dec(v_x_415_);
v___x_432_ = lean_box(0);
return v___x_432_;
}
else
{
v_x_414_ = v___x_430_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_getInductiveOverride_x3f_spec__0___redArg___boxed(lean_object* v_as_434_, lean_object* v_k_435_, lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Array_binSearchAux___at___00Lean_Compiler_getInductiveOverride_x3f_spec__0___redArg(v_as_434_, v_k_435_, v_x_436_, v_x_437_);
lean_dec_ref(v_k_435_);
lean_dec_ref(v_as_434_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getInductiveOverride_x3f(lean_object* v_env_439_, lean_object* v_declName_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_box(1);
v___x_442_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_439_, v_declName_440_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v___x_443_; lean_object* v_toEnvExtension_444_; lean_object* v_asyncMode_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_443_ = l_Lean_Compiler_inductiveOverrideExt;
v_toEnvExtension_444_ = lean_ctor_get(v___x_443_, 0);
v_asyncMode_445_ = lean_ctor_get(v_toEnvExtension_444_, 2);
lean_inc(v_declName_440_);
v___x_446_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_441_, v___x_443_, v_env_439_, v_asyncMode_445_, v_declName_440_);
v___x_447_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_446_, v_declName_440_);
lean_dec(v_declName_440_);
lean_dec(v___x_446_);
return v___x_447_;
}
else
{
lean_object* v_val_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v_entries_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_val_448_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_val_448_);
lean_dec_ref_known(v___x_442_, 1);
v___x_449_ = l_Lean_Compiler_inductiveOverrideExt;
v___x_450_ = 0;
v_entries_451_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_441_, v___x_449_, v_env_439_, v_val_448_, v___x_450_);
lean_dec(v_val_448_);
lean_dec_ref(v_env_439_);
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = lean_array_get_size(v_entries_451_);
v___x_454_ = lean_nat_dec_lt(v___x_452_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_dec_ref(v_entries_451_);
lean_dec(v_declName_440_);
v___x_455_ = lean_box(0);
return v___x_455_;
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_nat_sub(v___x_453_, v___x_456_);
v___x_458_ = lean_nat_dec_le(v___x_452_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec(v___x_457_);
lean_dec_ref(v_entries_451_);
lean_dec(v_declName_440_);
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_obj_once(&l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__2, &l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__2_once, _init_l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__2);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v_declName_440_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = l_Array_binSearchAux___at___00Lean_Compiler_getInductiveOverride_x3f_spec__0___redArg(v_entries_451_, v___x_461_, v___x_452_, v___x_457_);
lean_dec_ref_known(v___x_461_, 2);
lean_dec_ref(v_entries_451_);
return v___x_462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_getInductiveOverride_x3f_spec__0(lean_object* v_as_463_, lean_object* v_k_464_, lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Array_binSearchAux___at___00Lean_Compiler_getInductiveOverride_x3f_spec__0___redArg(v_as_463_, v_k_464_, v_x_465_, v_x_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_getInductiveOverride_x3f_spec__0___boxed(lean_object* v_as_469_, lean_object* v_k_470_, lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Array_binSearchAux___at___00Lean_Compiler_getInductiveOverride_x3f_spec__0(v_as_469_, v_k_470_, v_x_471_, v_x_472_, v_x_473_);
lean_dec_ref(v_k_470_);
lean_dec_ref(v_as_469_);
return v_res_474_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Compiler_hasInductiveOverride_spec__0___redArg(lean_object* v_as_475_, lean_object* v_k_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v_m_481_; lean_object* v_a_482_; uint8_t v___x_483_; 
v___x_479_ = lean_nat_add(v_x_477_, v_x_478_);
v___x_480_ = lean_unsigned_to_nat(1u);
v_m_481_ = lean_nat_shiftr(v___x_479_, v___x_480_);
lean_dec(v___x_479_);
v_a_482_ = lean_array_fget_borrowed(v_as_475_, v_m_481_);
v___x_483_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_482_, v_k_476_);
if (v___x_483_ == 0)
{
uint8_t v___x_484_; 
lean_dec(v_x_478_);
v___x_484_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_476_, v_a_482_);
if (v___x_484_ == 0)
{
uint8_t v___x_485_; 
lean_dec(v_m_481_);
lean_dec(v_x_477_);
v___x_485_ = 1;
return v___x_485_;
}
else
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_nat_dec_eq(v_m_481_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_nat_sub(v_m_481_, v___x_480_);
lean_dec(v_m_481_);
v___x_489_ = lean_nat_dec_lt(v___x_488_, v_x_477_);
if (v___x_489_ == 0)
{
v_x_478_ = v___x_488_;
goto _start;
}
else
{
lean_dec(v___x_488_);
lean_dec(v_x_477_);
return v___x_483_;
}
}
else
{
lean_dec(v_m_481_);
lean_dec(v_x_477_);
return v___x_483_;
}
}
}
else
{
lean_object* v___x_491_; uint8_t v___x_492_; 
lean_dec(v_x_477_);
v___x_491_ = lean_nat_add(v_m_481_, v___x_480_);
lean_dec(v_m_481_);
v___x_492_ = lean_nat_dec_le(v___x_491_, v_x_478_);
if (v___x_492_ == 0)
{
lean_dec(v___x_491_);
lean_dec(v_x_478_);
return v___x_492_;
}
else
{
v_x_477_ = v___x_491_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_hasInductiveOverride_spec__0___redArg___boxed(lean_object* v_as_494_, lean_object* v_k_495_, lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
uint8_t v_res_498_; lean_object* v_r_499_; 
v_res_498_ = l_Array_binSearchAux___at___00Lean_Compiler_hasInductiveOverride_spec__0___redArg(v_as_494_, v_k_495_, v_x_496_, v_x_497_);
lean_dec_ref(v_k_495_);
lean_dec_ref(v_as_494_);
v_r_499_ = lean_box(v_res_498_);
return v_r_499_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasInductiveOverride(lean_object* v_env_500_, lean_object* v_declName_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_box(1);
v___x_503_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_500_, v_declName_501_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v___x_504_; lean_object* v_toEnvExtension_505_; lean_object* v_asyncMode_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_504_ = l_Lean_Compiler_inductiveOverrideExt;
v_toEnvExtension_505_ = lean_ctor_get(v___x_504_, 0);
v_asyncMode_506_ = lean_ctor_get(v_toEnvExtension_505_, 2);
lean_inc(v_declName_501_);
v___x_507_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_502_, v___x_504_, v_env_500_, v_asyncMode_506_, v_declName_501_);
v___x_508_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_501_, v___x_507_);
lean_dec(v___x_507_);
lean_dec(v_declName_501_);
return v___x_508_;
}
else
{
lean_object* v_val_509_; lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v_entries_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_val_509_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_val_509_);
lean_dec_ref_known(v___x_503_, 1);
v___x_510_ = l_Lean_Compiler_inductiveOverrideExt;
v___x_511_ = 0;
v_entries_512_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_502_, v___x_510_, v_env_500_, v_val_509_, v___x_511_);
lean_dec(v_val_509_);
lean_dec_ref(v_env_500_);
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_array_get_size(v_entries_512_);
v___x_515_ = lean_nat_dec_lt(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_dec_ref(v_entries_512_);
lean_dec(v_declName_501_);
return v___x_515_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_sub(v___x_514_, v___x_516_);
v___x_518_ = lean_nat_dec_le(v___x_513_, v___x_517_);
if (v___x_518_ == 0)
{
lean_dec(v___x_517_);
lean_dec_ref(v_entries_512_);
lean_dec(v_declName_501_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_519_ = lean_obj_once(&l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__2, &l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__2_once, _init_l_Lean_Compiler_instInhabitedInductiveOverride_default___closed__2);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_declName_501_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l_Array_binSearchAux___at___00Lean_Compiler_hasInductiveOverride_spec__0___redArg(v_entries_512_, v___x_520_, v___x_513_, v___x_517_);
lean_dec_ref_known(v___x_520_, 2);
lean_dec_ref(v_entries_512_);
return v___x_521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasInductiveOverride___boxed(lean_object* v_env_522_, lean_object* v_declName_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l_Lean_Compiler_hasInductiveOverride(v_env_522_, v_declName_523_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Compiler_hasInductiveOverride_spec__0(lean_object* v_as_526_, lean_object* v_k_527_, lean_object* v_x_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = l_Array_binSearchAux___at___00Lean_Compiler_hasInductiveOverride_spec__0___redArg(v_as_526_, v_k_527_, v_x_528_, v_x_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_hasInductiveOverride_spec__0___boxed(lean_object* v_as_532_, lean_object* v_k_533_, lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
uint8_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = l_Array_binSearchAux___at___00Lean_Compiler_hasInductiveOverride_spec__0(v_as_532_, v_k_533_, v_x_534_, v_x_535_, v_x_536_);
lean_dec_ref(v_k_533_);
lean_dec_ref(v_as_532_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0(lean_object* v_msg_546_){
_start:
{
lean_object* v___f_547_; lean_object* v___f_548_; lean_object* v___f_549_; lean_object* v___f_550_; lean_object* v___f_551_; lean_object* v___f_552_; lean_object* v___f_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___f_547_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__0));
v___f_548_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__1));
v___f_549_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__2));
v___f_550_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__3));
v___f_551_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__4));
v___f_552_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__5));
v___f_553_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__6));
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___f_547_);
lean_ctor_set(v___x_554_, 1, v___f_548_);
v___x_555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v___f_549_);
lean_ctor_set(v___x_555_, 2, v___f_550_);
lean_ctor_set(v___x_555_, 3, v___f_551_);
lean_ctor_set(v___x_555_, 4, v___f_552_);
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___f_553_);
v___x_557_ = lean_box(0);
v___x_558_ = l_instInhabitedOfMonad___redArg(v___x_556_, v___x_557_);
v___x_559_ = lean_panic_fn_borrowed(v___x_558_, v_msg_546_);
lean_dec(v___x_558_);
return v___x_559_;
}
}
static lean_object* _init_l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__2(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_562_ = ((lean_object*)(l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__1));
v___x_563_ = lean_unsigned_to_nat(78u);
v___x_564_ = lean_unsigned_to_nat(118u);
v___x_565_ = ((lean_object*)(l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__0));
v___x_566_ = ((lean_object*)(l_Lean_Compiler_addInductiveOverride___closed__2));
v___x_567_ = l_mkPanicMessageWithDecl(v___x_566_, v___x_565_, v___x_564_, v___x_563_, v___x_562_);
return v___x_567_;
}
}
static lean_object* _init_l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__3(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_568_ = ((lean_object*)(l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__1));
v___x_569_ = lean_unsigned_to_nat(53u);
v___x_570_ = lean_unsigned_to_nat(117u);
v___x_571_ = ((lean_object*)(l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__0));
v___x_572_ = ((lean_object*)(l_Lean_Compiler_addInductiveOverride___closed__2));
v___x_573_ = l_mkPanicMessageWithDecl(v___x_572_, v___x_571_, v___x_570_, v___x_569_, v___x_568_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct(lean_object* v_type_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = l_Lean_Expr_getForallBody(v_type_574_);
v___x_576_ = l_Lean_Expr_appArg_x21(v___x_575_);
lean_dec_ref(v___x_575_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_deBruijnIndex_577_; lean_object* v_depth_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_deBruijnIndex_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_deBruijnIndex_577_);
lean_dec_ref_known(v___x_576_, 1);
lean_inc_ref(v_type_574_);
v_depth_578_ = l_Lean_Expr_getForallArity(v_type_574_);
v___x_579_ = lean_nat_sub(v_depth_578_, v_deBruijnIndex_577_);
lean_dec(v_deBruijnIndex_577_);
lean_dec(v_depth_578_);
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_nat_sub(v___x_579_, v___x_580_);
lean_dec(v___x_579_);
v___x_582_ = l_Lean_Expr_getForallBodyMaxDepth(v___x_581_, v_type_574_);
lean_dec_ref(v_type_574_);
if (lean_obj_tag(v___x_582_) == 7)
{
lean_object* v_binderType_583_; lean_object* v___x_584_; lean_object* v_indTypeName_585_; 
v_binderType_583_ = lean_ctor_get(v___x_582_, 1);
lean_inc_ref(v_binderType_583_);
lean_dec_ref_known(v___x_582_, 3);
v___x_584_ = l_Lean_Expr_getAppFn(v_binderType_583_);
lean_dec_ref(v_binderType_583_);
v_indTypeName_585_ = l_Lean_Expr_constName_x21(v___x_584_);
lean_dec_ref(v___x_584_);
return v_indTypeName_585_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec_ref(v___x_582_);
v___x_586_ = lean_obj_once(&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__2, &l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__2_once, _init_l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__2);
v___x_587_ = l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0(v___x_586_);
return v___x_587_;
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_dec_ref(v___x_576_);
lean_dec_ref(v_type_574_);
v___x_588_ = lean_obj_once(&l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__3, &l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__3_once, _init_l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__3);
v___x_589_ = l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0(v___x_588_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getCasesInfoOverride_x3f(lean_object* v_declName_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___y_595_; uint8_t v___y_596_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___x_647_; lean_object* v_env_648_; lean_object* v___x_649_; 
v___x_647_ = lean_st_ref_get(v_a_592_);
v_env_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_ref(v_env_648_);
lean_dec(v___x_647_);
lean_inc(v_declName_590_);
v___x_649_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_648_, v_declName_590_);
if (lean_obj_tag(v___x_649_) == 1)
{
lean_object* v_val_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_674_; 
v_val_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_674_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_674_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_val_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_674_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
if (lean_obj_tag(v_val_650_) == 3)
{
lean_object* v___x_654_; 
lean_dec_ref_known(v_val_650_, 1);
v___x_654_ = l_Lean_getCasesInfo(v_declName_590_, v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_665_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_665_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_665_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_665_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v_a_655_);
v___x_660_ = v___x_652_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_664_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_662_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_660_);
v___x_662_ = v___x_657_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_del_object(v___x_652_);
v_a_666_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_654_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_654_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
lean_del_object(v___x_652_);
lean_dec(v_val_650_);
v___y_602_ = v_a_591_;
v___y_603_ = v_a_592_;
goto v___jp_601_;
}
}
}
else
{
lean_dec(v___x_649_);
v___y_602_ = v_a_591_;
v___y_603_ = v_a_592_;
goto v___jp_601_;
}
v___jp_594_:
{
if (v___y_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v___y_595_);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec_ref(v___y_595_);
v___x_599_ = lean_box(0);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
v___jp_601_:
{
lean_object* v___x_604_; lean_object* v_env_605_; uint8_t v___x_606_; 
v___x_604_ = lean_st_ref_get(v___y_603_);
v_env_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc_ref(v_env_605_);
lean_dec(v___x_604_);
lean_inc(v_declName_590_);
v___x_606_ = l_Lean_isSparseCasesOn(v_env_605_, v_declName_590_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v_env_608_; uint8_t v___x_609_; 
v___x_607_ = lean_st_ref_get(v___y_603_);
v_env_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc_ref(v_env_608_);
lean_dec(v___x_607_);
lean_inc(v_declName_590_);
v___x_609_ = l_Lean_isCasesOnRecursor(v_env_608_, v_declName_590_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec(v_declName_590_);
v___x_610_ = lean_box(0);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
else
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_getCasesInfo(v_declName_590_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_env_616_; lean_object* v_indName_617_; uint8_t v___x_618_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
v___x_614_ = lean_st_ref_get(v___y_603_);
v___x_615_ = lean_st_ref_get(v___y_603_);
v_env_616_ = lean_ctor_get(v___x_614_, 0);
lean_inc_ref(v_env_616_);
lean_dec(v___x_614_);
v_indName_617_ = lean_ctor_get(v_a_613_, 1);
lean_inc(v_indName_617_);
v___x_618_ = l_Lean_Compiler_hasInductiveOverride(v_env_616_, v_indName_617_);
if (v___x_618_ == 0)
{
lean_dec(v___x_615_);
v___y_595_ = v_a_613_;
v___y_596_ = v___x_618_;
goto v___jp_594_;
}
else
{
lean_object* v_env_619_; uint8_t v___x_620_; 
v_env_619_ = lean_ctor_get(v___x_615_, 0);
lean_inc_ref(v_env_619_);
lean_dec(v___x_615_);
lean_inc(v_indName_617_);
v___x_620_ = l_Lean_isStructure(v_env_619_, v_indName_617_);
if (v___x_620_ == 0)
{
v___y_595_ = v_a_613_;
v___y_596_ = v___x_618_;
goto v___jp_594_;
}
else
{
v___y_595_ = v_a_613_;
v___y_596_ = v___x_606_;
goto v___jp_594_;
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
v_a_621_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_612_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_612_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
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
else
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_getCasesInfo(v_declName_590_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_638_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_638_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_634_, 0, v_a_630_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_634_);
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
v_a_639_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_629_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_629_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getCasesInfoOverride_x3f___boxed(lean_object* v_declName_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Compiler_getCasesInfoOverride_x3f(v_declName_675_, v_a_676_, v_a_677_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_679_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isCasesOnLikeOverride(lean_object* v_env_680_, lean_object* v_declName_681_){
_start:
{
lean_object* v___x_692_; 
lean_inc(v_declName_681_);
lean_inc_ref(v_env_680_);
v___x_692_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_680_, v_declName_681_);
if (lean_obj_tag(v___x_692_) == 1)
{
lean_object* v_val_693_; 
v_val_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_val_693_);
lean_dec_ref_known(v___x_692_, 1);
if (lean_obj_tag(v_val_693_) == 3)
{
uint8_t v___x_694_; 
lean_dec_ref_known(v_val_693_, 1);
lean_dec(v_declName_681_);
lean_dec_ref(v_env_680_);
v___x_694_ = 1;
return v___x_694_;
}
else
{
lean_dec(v_val_693_);
goto v___jp_682_;
}
}
else
{
lean_dec(v___x_692_);
goto v___jp_682_;
}
v___jp_682_:
{
uint8_t v___x_683_; uint8_t v___x_684_; 
lean_inc(v_declName_681_);
lean_inc_ref(v_env_680_);
v___x_683_ = l_Lean_isSparseCasesOn(v_env_680_, v_declName_681_);
v___x_684_ = 1;
if (v___x_683_ == 0)
{
uint8_t v___x_685_; 
lean_inc(v_declName_681_);
lean_inc_ref(v_env_680_);
v___x_685_ = l_Lean_isCasesOnRecursor(v_env_680_, v_declName_681_);
if (v___x_685_ == 0)
{
lean_dec(v_declName_681_);
lean_dec_ref(v_env_680_);
return v___x_685_;
}
else
{
lean_object* v___x_686_; 
lean_inc_ref(v_env_680_);
v___x_686_ = l_Lean_Environment_findConstVal_x3f(v_env_680_, v_declName_681_, v___x_683_);
if (lean_obj_tag(v___x_686_) == 1)
{
lean_object* v_val_687_; lean_object* v_type_688_; lean_object* v_indName_689_; uint8_t v___x_690_; 
v_val_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_val_687_);
lean_dec_ref_known(v___x_686_, 1);
v_type_688_ = lean_ctor_get(v_val_687_, 2);
lean_inc_ref(v_type_688_);
lean_dec(v_val_687_);
v_indName_689_ = l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct(v_type_688_);
lean_inc(v_indName_689_);
lean_inc_ref(v_env_680_);
v___x_690_ = l_Lean_Compiler_hasInductiveOverride(v_env_680_, v_indName_689_);
if (v___x_690_ == 0)
{
lean_dec(v_indName_689_);
lean_dec_ref(v_env_680_);
return v___x_684_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = l_Lean_isStructure(v_env_680_, v_indName_689_);
return v___x_691_;
}
}
else
{
lean_dec(v___x_686_);
lean_dec_ref(v_env_680_);
return v___x_683_;
}
}
}
else
{
lean_dec(v_declName_681_);
lean_dec_ref(v_env_680_);
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isCasesOnLikeOverride___boxed(lean_object* v_env_695_, lean_object* v_declName_696_){
_start:
{
uint8_t v_res_697_; lean_object* v_r_698_; 
v_res_697_ = l_Lean_Compiler_isCasesOnLikeOverride(v_env_695_, v_declName_696_);
v_r_698_ = lean_box(v_res_697_);
return v_r_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getProjectionFnInfoOverride_x3f(lean_object* v_env_699_, lean_object* v_declName_700_){
_start:
{
lean_object* v___x_714_; 
lean_inc(v_declName_700_);
lean_inc_ref(v_env_699_);
v___x_714_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_699_, v_declName_700_);
if (lean_obj_tag(v___x_714_) == 1)
{
lean_object* v_val_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_723_; 
v_val_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_723_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_val_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
if (lean_obj_tag(v_val_715_) == 4)
{
lean_object* v_info_719_; lean_object* v___x_721_; 
lean_dec(v_declName_700_);
lean_dec_ref(v_env_699_);
v_info_719_ = lean_ctor_get(v_val_715_, 1);
lean_inc_ref(v_info_719_);
lean_dec_ref_known(v_val_715_, 2);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v_info_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_info_719_);
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
lean_del_object(v___x_717_);
lean_dec(v_val_715_);
goto v___jp_701_;
}
}
}
else
{
lean_dec(v___x_714_);
goto v___jp_701_;
}
v___jp_701_:
{
lean_object* v___x_702_; 
lean_inc_ref(v_env_699_);
v___x_702_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_699_, v_declName_700_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_dec_ref(v_env_699_);
return v___x_702_;
}
else
{
lean_object* v_val_703_; lean_object* v_ctorName_704_; uint8_t v___x_705_; lean_object* v___x_706_; 
v_val_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_val_703_);
v_ctorName_704_ = lean_ctor_get(v_val_703_, 0);
lean_inc(v_ctorName_704_);
lean_dec(v_val_703_);
v___x_705_ = 0;
lean_inc_ref(v_env_699_);
v___x_706_ = l_Lean_Environment_find_x3f(v_env_699_, v_ctorName_704_, v___x_705_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v___x_707_; 
lean_dec_ref_known(v___x_702_, 1);
lean_dec_ref(v_env_699_);
v___x_707_ = lean_box(0);
return v___x_707_;
}
else
{
lean_object* v_val_708_; 
v_val_708_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v___x_706_, 1);
if (lean_obj_tag(v_val_708_) == 6)
{
lean_object* v_val_709_; lean_object* v_induct_710_; uint8_t v___x_711_; 
v_val_709_ = lean_ctor_get(v_val_708_, 0);
lean_inc_ref(v_val_709_);
lean_dec_ref_known(v_val_708_, 1);
v_induct_710_ = lean_ctor_get(v_val_709_, 1);
lean_inc(v_induct_710_);
lean_dec_ref(v_val_709_);
v___x_711_ = l_Lean_Compiler_hasInductiveOverride(v_env_699_, v_induct_710_);
if (v___x_711_ == 0)
{
return v___x_702_;
}
else
{
lean_object* v___x_712_; 
lean_dec_ref_known(v___x_702_, 1);
v___x_712_ = lean_box(0);
return v___x_712_;
}
}
else
{
lean_object* v___x_713_; 
lean_dec(v_val_708_);
lean_dec_ref_known(v___x_702_, 1);
lean_dec_ref(v_env_699_);
v___x_713_ = lean_box(0);
return v___x_713_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isProjectionFnOverride(lean_object* v_env_724_, lean_object* v_declName_725_){
_start:
{
lean_object* v___y_727_; lean_object* v___x_740_; 
lean_inc(v_declName_725_);
lean_inc_ref(v_env_724_);
v___x_740_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_724_, v_declName_725_);
if (lean_obj_tag(v___x_740_) == 1)
{
lean_object* v_val_741_; 
v_val_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_val_741_);
lean_dec_ref_known(v___x_740_, 1);
if (lean_obj_tag(v_val_741_) == 4)
{
uint8_t v___x_742_; 
lean_dec_ref_known(v_val_741_, 2);
lean_dec(v_declName_725_);
lean_dec_ref(v_env_724_);
v___x_742_ = 1;
return v___x_742_;
}
else
{
lean_dec(v_val_741_);
goto v___jp_730_;
}
}
else
{
lean_dec(v___x_740_);
goto v___jp_730_;
}
v___jp_726_:
{
if (lean_obj_tag(v___y_727_) == 0)
{
uint8_t v___x_728_; 
v___x_728_ = 0;
return v___x_728_;
}
else
{
uint8_t v___x_729_; 
lean_dec_ref_known(v___y_727_, 1);
v___x_729_ = 1;
return v___x_729_;
}
}
v___jp_730_:
{
lean_object* v___x_731_; 
lean_inc_ref(v_env_724_);
v___x_731_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_724_, v_declName_725_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_dec_ref(v_env_724_);
v___y_727_ = v___x_731_;
goto v___jp_726_;
}
else
{
lean_object* v_val_732_; lean_object* v_ctorName_733_; uint8_t v___x_734_; lean_object* v___x_735_; 
v_val_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_val_732_);
v_ctorName_733_ = lean_ctor_get(v_val_732_, 0);
lean_inc(v_ctorName_733_);
lean_dec(v_val_732_);
v___x_734_ = 0;
lean_inc_ref(v_env_724_);
v___x_735_ = l_Lean_Environment_find_x3f(v_env_724_, v_ctorName_733_, v___x_734_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_dec_ref_known(v___x_731_, 1);
lean_dec_ref(v_env_724_);
return v___x_734_;
}
else
{
lean_object* v_val_736_; 
v_val_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_val_736_);
lean_dec_ref_known(v___x_735_, 1);
if (lean_obj_tag(v_val_736_) == 6)
{
lean_object* v_val_737_; lean_object* v_induct_738_; uint8_t v___x_739_; 
v_val_737_ = lean_ctor_get(v_val_736_, 0);
lean_inc_ref(v_val_737_);
lean_dec_ref_known(v_val_736_, 1);
v_induct_738_ = lean_ctor_get(v_val_737_, 1);
lean_inc(v_induct_738_);
lean_dec_ref(v_val_737_);
v___x_739_ = l_Lean_Compiler_hasInductiveOverride(v_env_724_, v_induct_738_);
if (v___x_739_ == 0)
{
v___y_727_ = v___x_731_;
goto v___jp_726_;
}
else
{
lean_dec_ref_known(v___x_731_, 1);
return v___x_734_;
}
}
else
{
lean_dec(v_val_736_);
lean_dec_ref_known(v___x_731_, 1);
lean_dec_ref(v_env_724_);
return v___x_734_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isProjectionFnOverride___boxed(lean_object* v_env_743_, lean_object* v_declName_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_Lean_Compiler_isProjectionFnOverride(v_env_743_, v_declName_744_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isCtorOverrideSimple_x3f(lean_object* v_env_747_, lean_object* v_declName_748_){
_start:
{
lean_object* v___x_770_; 
lean_inc(v_declName_748_);
lean_inc_ref(v_env_747_);
v___x_770_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_747_, v_declName_748_);
if (lean_obj_tag(v___x_770_) == 1)
{
lean_object* v_val_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_779_; 
v_val_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_779_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_779_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_val_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_779_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
if (lean_obj_tag(v_val_771_) == 2)
{
lean_object* v_info_775_; lean_object* v___x_777_; 
lean_dec(v_declName_748_);
lean_dec_ref(v_env_747_);
v_info_775_ = lean_ctor_get(v_val_771_, 1);
lean_inc_ref(v_info_775_);
lean_dec_ref_known(v_val_771_, 2);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_info_775_);
v___x_777_ = v___x_773_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_info_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
else
{
lean_del_object(v___x_773_);
lean_dec(v_val_771_);
goto v___jp_749_;
}
}
}
else
{
lean_dec(v___x_770_);
goto v___jp_749_;
}
v___jp_749_:
{
uint8_t v___x_750_; lean_object* v___x_751_; 
v___x_750_ = 0;
lean_inc_ref(v_env_747_);
v___x_751_ = l_Lean_Environment_find_x3f(v_env_747_, v_declName_748_, v___x_750_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v___x_752_; 
lean_dec_ref(v_env_747_);
v___x_752_ = lean_box(0);
return v___x_752_;
}
else
{
lean_object* v_val_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_769_; 
v_val_753_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_769_ == 0)
{
v___x_755_ = v___x_751_;
v_isShared_756_ = v_isSharedCheck_769_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_val_753_);
lean_dec(v___x_751_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_769_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
if (lean_obj_tag(v_val_753_) == 6)
{
lean_object* v_val_757_; lean_object* v_induct_758_; lean_object* v_cidx_759_; lean_object* v_numParams_760_; lean_object* v_numFields_761_; uint8_t v___x_762_; 
v_val_757_ = lean_ctor_get(v_val_753_, 0);
lean_inc_ref(v_val_757_);
lean_dec_ref_known(v_val_753_, 1);
v_induct_758_ = lean_ctor_get(v_val_757_, 1);
lean_inc_n(v_induct_758_, 2);
v_cidx_759_ = lean_ctor_get(v_val_757_, 2);
lean_inc(v_cidx_759_);
v_numParams_760_ = lean_ctor_get(v_val_757_, 3);
lean_inc(v_numParams_760_);
v_numFields_761_ = lean_ctor_get(v_val_757_, 4);
lean_inc(v_numFields_761_);
lean_dec_ref(v_val_757_);
v___x_762_ = l_Lean_Compiler_hasInductiveOverride(v_env_747_, v_induct_758_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_763_, 0, v_induct_758_);
lean_ctor_set(v___x_763_, 1, v_cidx_759_);
lean_ctor_set(v___x_763_, 2, v_numParams_760_);
lean_ctor_set(v___x_763_, 3, v_numFields_761_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_763_);
v___x_765_ = v___x_755_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
else
{
lean_object* v___x_767_; 
lean_dec(v_numFields_761_);
lean_dec(v_numParams_760_);
lean_dec(v_cidx_759_);
lean_dec(v_induct_758_);
lean_del_object(v___x_755_);
v___x_767_ = lean_box(0);
return v___x_767_;
}
}
else
{
lean_object* v___x_768_; 
lean_del_object(v___x_755_);
lean_dec(v_val_753_);
lean_dec_ref(v_env_747_);
v___x_768_ = lean_box(0);
return v___x_768_;
}
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_instMonadEIO(lean_box(0));
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0(lean_object* v_msg_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v_toApplicative_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_820_; 
v___x_787_ = lean_obj_once(&l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___closed__0, &l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___closed__0);
v___x_788_ = l_StateRefT_x27_instMonad___redArg(v___x_787_);
v_toApplicative_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v___x_788_, 1);
lean_dec(v_unused_821_);
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_820_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_toApplicative_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_820_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_toFunctor_793_; lean_object* v_toSeq_794_; lean_object* v_toSeqLeft_795_; lean_object* v_toSeqRight_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_818_; 
v_toFunctor_793_ = lean_ctor_get(v_toApplicative_789_, 0);
v_toSeq_794_ = lean_ctor_get(v_toApplicative_789_, 2);
v_toSeqLeft_795_ = lean_ctor_get(v_toApplicative_789_, 3);
v_toSeqRight_796_ = lean_ctor_get(v_toApplicative_789_, 4);
v_isSharedCheck_818_ = !lean_is_exclusive(v_toApplicative_789_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v_toApplicative_789_, 1);
lean_dec(v_unused_819_);
v___x_798_ = v_toApplicative_789_;
v_isShared_799_ = v_isSharedCheck_818_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_toSeqRight_796_);
lean_inc(v_toSeqLeft_795_);
lean_inc(v_toSeq_794_);
lean_inc(v_toFunctor_793_);
lean_dec(v_toApplicative_789_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_818_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___f_803_; lean_object* v___x_804_; lean_object* v___f_805_; lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___x_809_; 
v___f_800_ = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___closed__1));
v___f_801_ = ((lean_object*)(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_793_);
v___f_802_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_802_, 0, v_toFunctor_793_);
v___f_803_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_803_, 0, v_toFunctor_793_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___f_802_);
lean_ctor_set(v___x_804_, 1, v___f_803_);
v___f_805_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_805_, 0, v_toSeqRight_796_);
v___f_806_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_806_, 0, v_toSeqLeft_795_);
v___f_807_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_807_, 0, v_toSeq_794_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 4, v___f_805_);
lean_ctor_set(v___x_798_, 3, v___f_806_);
lean_ctor_set(v___x_798_, 2, v___f_807_);
lean_ctor_set(v___x_798_, 1, v___f_800_);
lean_ctor_set(v___x_798_, 0, v___x_804_);
v___x_809_ = v___x_798_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___f_800_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v___f_807_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v___f_806_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v___f_805_);
v___x_809_ = v_reuseFailAlloc_817_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___f_801_);
lean_ctor_set(v___x_791_, 0, v___x_809_);
v___x_811_ = v___x_791_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___f_801_);
v___x_811_ = v_reuseFailAlloc_816_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_1468__overap_814_; lean_object* v___x_815_; 
v___x_812_ = lean_box(0);
v___x_813_ = l_instInhabitedOfMonad___redArg(v___x_811_, v___x_812_);
v___x_1468__overap_814_ = lean_panic_fn_borrowed(v___x_813_, v_msg_783_);
lean_dec(v___x_813_);
lean_inc(v___y_785_);
lean_inc_ref(v___y_784_);
v___x_815_ = lean_apply_3(v___x_1468__overap_814_, v___y_784_, v___y_785_, lean_box(0));
return v___x_815_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0___boxed(lean_object* v_msg_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0(v_msg_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_826_;
}
}
static lean_object* _init_l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___closed__2(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_829_ = ((lean_object*)(l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__1));
v___x_830_ = lean_unsigned_to_nat(11u);
v___x_831_ = lean_unsigned_to_nat(122u);
v___x_832_ = ((lean_object*)(l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___closed__1));
v___x_833_ = ((lean_object*)(l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___closed__0));
v___x_834_ = l_mkPanicMessageWithDecl(v___x_833_, v___x_832_, v___x_831_, v___x_830_, v___x_829_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0(lean_object* v_constName_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; lean_object* v_env_843_; uint8_t v___x_844_; lean_object* v___x_845_; 
v___x_839_ = lean_st_ref_get(v___y_837_);
v_env_843_ = lean_ctor_get(v___x_839_, 0);
lean_inc_ref(v_env_843_);
lean_dec(v___x_839_);
v___x_844_ = 0;
v___x_845_ = l_Lean_Environment_findAsync_x3f(v_env_843_, v_constName_835_, v___x_844_);
if (lean_obj_tag(v___x_845_) == 1)
{
lean_object* v_val_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_865_; 
v_val_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_865_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_865_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_val_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_865_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
uint8_t v_kind_850_; 
v_kind_850_ = lean_ctor_get_uint8(v_val_846_, sizeof(void*)*3);
if (v_kind_850_ == 6)
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_846_);
if (lean_obj_tag(v___x_851_) == 6)
{
lean_object* v_val_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_862_; 
v_val_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_862_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_val_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v_val_852_);
v___x_857_ = v___x_848_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_val_852_);
v___x_857_ = v_reuseFailAlloc_861_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_859_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set_tag(v___x_854_, 0);
lean_ctor_set(v___x_854_, 0, v___x_857_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec_ref(v___x_851_);
lean_del_object(v___x_848_);
v___x_863_ = lean_obj_once(&l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___closed__2, &l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___closed__2_once, _init_l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___closed__2);
v___x_864_ = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0_spec__0(v___x_863_, v___y_836_, v___y_837_);
return v___x_864_;
}
}
else
{
lean_del_object(v___x_848_);
lean_dec(v_val_846_);
goto v___jp_840_;
}
}
}
else
{
lean_dec(v___x_845_);
goto v___jp_840_;
}
v___jp_840_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_box(0);
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0___boxed(lean_object* v_constName_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0(v_constName_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_870_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_871_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__0);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__2(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_874_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__1);
v___x_875_ = lean_unsigned_to_nat(0u);
v___x_876_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
lean_ctor_set(v___x_876_, 2, v___x_875_);
lean_ctor_set(v___x_876_, 3, v___x_875_);
lean_ctor_set(v___x_876_, 4, v___x_874_);
lean_ctor_set(v___x_876_, 5, v___x_874_);
lean_ctor_set(v___x_876_, 6, v___x_874_);
lean_ctor_set(v___x_876_, 7, v___x_874_);
lean_ctor_set(v___x_876_, 8, v___x_874_);
lean_ctor_set(v___x_876_, 9, v___x_874_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__3(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = lean_unsigned_to_nat(32u);
v___x_878_ = lean_mk_empty_array_with_capacity(v___x_877_);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__4(void){
_start:
{
size_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_880_ = ((size_t)5ULL);
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = lean_unsigned_to_nat(32u);
v___x_883_ = lean_mk_empty_array_with_capacity(v___x_882_);
v___x_884_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__3);
v___x_885_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_883_);
lean_ctor_set(v___x_885_, 2, v___x_881_);
lean_ctor_set(v___x_885_, 3, v___x_881_);
lean_ctor_set_usize(v___x_885_, 4, v___x_880_);
return v___x_885_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__5(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_886_ = lean_box(1);
v___x_887_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__4);
v___x_888_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__1);
v___x_889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_887_);
lean_ctor_set(v___x_889_, 2, v___x_886_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(lean_object* v_msgData_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; lean_object* v_env_895_; lean_object* v_options_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_894_ = lean_st_ref_get(v___y_892_);
v_env_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc_ref(v_env_895_);
lean_dec(v___x_894_);
v_options_896_ = lean_ctor_get(v___y_891_, 2);
v___x_897_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__2);
v___x_898_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__5);
lean_inc_ref(v_options_896_);
v___x_899_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_899_, 0, v_env_895_);
lean_ctor_set(v___x_899_, 1, v___x_897_);
lean_ctor_set(v___x_899_, 2, v___x_898_);
lean_ctor_set(v___x_899_, 3, v_options_896_);
v___x_900_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v_msgData_890_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___boxed(lean_object* v_msgData_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msgData_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_ref_911_; lean_object* v___x_912_; lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_921_; 
v_ref_911_ = lean_ctor_get(v___y_908_, 5);
v___x_912_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msg_907_, v___y_908_, v___y_909_);
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_921_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_919_; 
lean_inc(v_ref_911_);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_ref_911_);
lean_ctor_set(v___x_917_, 1, v_a_913_);
if (v_isShared_916_ == 0)
{
lean_ctor_set_tag(v___x_915_, 1);
lean_ctor_set(v___x_915_, 0, v___x_917_);
v___x_919_ = v___x_915_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_927_, lean_object* v_msg_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_fileName_932_; lean_object* v_fileMap_933_; lean_object* v_options_934_; lean_object* v_currRecDepth_935_; lean_object* v_maxRecDepth_936_; lean_object* v_ref_937_; lean_object* v_currNamespace_938_; lean_object* v_openDecls_939_; lean_object* v_initHeartbeats_940_; lean_object* v_maxHeartbeats_941_; lean_object* v_quotContext_942_; lean_object* v_currMacroScope_943_; uint8_t v_diag_944_; lean_object* v_cancelTk_x3f_945_; uint8_t v_suppressElabErrors_946_; lean_object* v_inheritedTraceOptions_947_; lean_object* v_ref_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_fileName_932_ = lean_ctor_get(v___y_929_, 0);
v_fileMap_933_ = lean_ctor_get(v___y_929_, 1);
v_options_934_ = lean_ctor_get(v___y_929_, 2);
v_currRecDepth_935_ = lean_ctor_get(v___y_929_, 3);
v_maxRecDepth_936_ = lean_ctor_get(v___y_929_, 4);
v_ref_937_ = lean_ctor_get(v___y_929_, 5);
v_currNamespace_938_ = lean_ctor_get(v___y_929_, 6);
v_openDecls_939_ = lean_ctor_get(v___y_929_, 7);
v_initHeartbeats_940_ = lean_ctor_get(v___y_929_, 8);
v_maxHeartbeats_941_ = lean_ctor_get(v___y_929_, 9);
v_quotContext_942_ = lean_ctor_get(v___y_929_, 10);
v_currMacroScope_943_ = lean_ctor_get(v___y_929_, 11);
v_diag_944_ = lean_ctor_get_uint8(v___y_929_, sizeof(void*)*14);
v_cancelTk_x3f_945_ = lean_ctor_get(v___y_929_, 12);
v_suppressElabErrors_946_ = lean_ctor_get_uint8(v___y_929_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_947_ = lean_ctor_get(v___y_929_, 13);
v_ref_948_ = l_Lean_replaceRef(v_ref_927_, v_ref_937_);
lean_inc_ref(v_inheritedTraceOptions_947_);
lean_inc(v_cancelTk_x3f_945_);
lean_inc(v_currMacroScope_943_);
lean_inc(v_quotContext_942_);
lean_inc(v_maxHeartbeats_941_);
lean_inc(v_initHeartbeats_940_);
lean_inc(v_openDecls_939_);
lean_inc(v_currNamespace_938_);
lean_inc(v_maxRecDepth_936_);
lean_inc(v_currRecDepth_935_);
lean_inc_ref(v_options_934_);
lean_inc_ref(v_fileMap_933_);
lean_inc_ref(v_fileName_932_);
v___x_949_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_949_, 0, v_fileName_932_);
lean_ctor_set(v___x_949_, 1, v_fileMap_933_);
lean_ctor_set(v___x_949_, 2, v_options_934_);
lean_ctor_set(v___x_949_, 3, v_currRecDepth_935_);
lean_ctor_set(v___x_949_, 4, v_maxRecDepth_936_);
lean_ctor_set(v___x_949_, 5, v_ref_948_);
lean_ctor_set(v___x_949_, 6, v_currNamespace_938_);
lean_ctor_set(v___x_949_, 7, v_openDecls_939_);
lean_ctor_set(v___x_949_, 8, v_initHeartbeats_940_);
lean_ctor_set(v___x_949_, 9, v_maxHeartbeats_941_);
lean_ctor_set(v___x_949_, 10, v_quotContext_942_);
lean_ctor_set(v___x_949_, 11, v_currMacroScope_943_);
lean_ctor_set(v___x_949_, 12, v_cancelTk_x3f_945_);
lean_ctor_set(v___x_949_, 13, v_inheritedTraceOptions_947_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*14, v_diag_944_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*14 + 1, v_suppressElabErrors_946_);
v___x_950_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_928_, v___x_949_, v___y_930_);
lean_dec_ref_known(v___x_949_, 14);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_951_, lean_object* v_msg_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_951_, v_msg_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v_ref_951_);
return v_res_956_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_962_ = l_Lean_stringToMessageData(v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_965_ = l_Lean_stringToMessageData(v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_974_ = l_Lean_stringToMessageData(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_977_ = l_Lean_stringToMessageData(v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_978_, lean_object* v_declHint_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; lean_object* v_env_983_; uint8_t v___x_984_; 
v___x_982_ = lean_st_ref_get(v___y_980_);
v_env_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc_ref(v_env_983_);
lean_dec(v___x_982_);
v___x_984_ = l_Lean_Name_isAnonymous(v_declHint_979_);
if (v___x_984_ == 0)
{
uint8_t v_isExporting_985_; 
v_isExporting_985_ = lean_ctor_get_uint8(v_env_983_, sizeof(void*)*8);
if (v_isExporting_985_ == 0)
{
lean_object* v___x_986_; 
lean_dec_ref(v_env_983_);
lean_dec(v_declHint_979_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v_msg_978_);
return v___x_986_;
}
else
{
lean_object* v___x_987_; uint8_t v___x_988_; 
lean_inc_ref(v_env_983_);
v___x_987_ = l_Lean_Environment_setExporting(v_env_983_, v___x_984_);
lean_inc(v_declHint_979_);
lean_inc_ref(v___x_987_);
v___x_988_ = l_Lean_Environment_contains(v___x_987_, v_declHint_979_, v_isExporting_985_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
lean_dec_ref(v___x_987_);
lean_dec_ref(v_env_983_);
lean_dec(v_declHint_979_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v_msg_978_);
return v___x_989_;
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_c_995_; lean_object* v___x_996_; 
v___x_990_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__2);
v___x_991_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___closed__5);
v___x_992_ = l_Lean_Options_empty;
v___x_993_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_993_, 0, v___x_987_);
lean_ctor_set(v___x_993_, 1, v___x_990_);
lean_ctor_set(v___x_993_, 2, v___x_991_);
lean_ctor_set(v___x_993_, 3, v___x_992_);
lean_inc(v_declHint_979_);
v___x_994_ = l_Lean_MessageData_ofConstName(v_declHint_979_, v___x_984_);
v_c_995_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_995_, 0, v___x_993_);
lean_ctor_set(v_c_995_, 1, v___x_994_);
v___x_996_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_983_, v_declHint_979_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec_ref(v_env_983_);
lean_dec(v_declHint_979_);
v___x_997_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v_c_995_);
v___x_999_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l_Lean_MessageData_note(v___x_1000_);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v_msg_978_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
else
{
lean_object* v_val_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1039_; 
v_val_1004_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1006_ = v___x_996_;
v_isShared_1007_ = v_isSharedCheck_1039_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_val_1004_);
lean_dec(v___x_996_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1039_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v_mod_1011_; uint8_t v___x_1012_; 
v___x_1008_ = lean_box(0);
v___x_1009_ = l_Lean_Environment_header(v_env_983_);
lean_dec_ref(v_env_983_);
v___x_1010_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1009_);
v_mod_1011_ = lean_array_get(v___x_1008_, v___x_1010_, v_val_1004_);
lean_dec(v_val_1004_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = l_Lean_isPrivateName(v_declHint_979_);
lean_dec(v_declHint_979_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1013_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v_c_995_);
v___x_1015_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Lean_MessageData_ofName(v_mod_1011_);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_MessageData_note(v___x_1020_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_msg_978_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set_tag(v___x_1006_, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1022_);
v___x_1024_ = v___x_1006_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1026_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v_c_995_);
v___x_1028_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = l_Lean_MessageData_ofName(v_mod_1011_);
v___x_1031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = l_Lean_MessageData_note(v___x_1033_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_msg_978_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set_tag(v___x_1006_, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1035_);
v___x_1037_ = v___x_1006_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1040_; 
lean_dec_ref(v_env_983_);
lean_dec(v_declHint_979_);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v_msg_978_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1041_, lean_object* v_declHint_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1041_, v_declHint_1042_, v___y_1043_);
lean_dec(v___y_1043_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1046_, lean_object* v_declHint_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1061_; 
v___x_1051_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1046_, v_declHint_1047_, v___y_1049_);
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1056_ = l_Lean_unknownIdentifierMessageTag;
v___x_1057_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v_a_1052_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1057_);
v___x_1059_ = v___x_1054_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1062_, lean_object* v_declHint_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1062_, v_declHint_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_ref_1068_, lean_object* v_msg_1069_, lean_object* v_declHint_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; lean_object* v_a_1075_; lean_object* v___x_1076_; 
v___x_1074_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1069_, v_declHint_1070_, v___y_1071_, v___y_1072_);
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref(v___x_1074_);
v___x_1076_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1068_, v_a_1075_, v___y_1071_, v___y_1072_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1077_, lean_object* v_msg_1078_, lean_object* v_declHint_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1077_, v_msg_1078_, v_declHint_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v_ref_1077_);
return v_res_1083_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__0));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l_Lean_Compiler_addInductiveOverride___closed__1));
v___x_1088_ = l_Lean_stringToMessageData(v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_1089_, lean_object* v_constName_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v___x_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1094_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_1095_ = 0;
lean_inc(v_constName_1090_);
v___x_1096_ = l_Lean_MessageData_ofConstName(v_constName_1090_, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1094_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__2);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1089_, v___x_1099_, v_constName_1090_, v___y_1091_, v___y_1092_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1101_, lean_object* v_constName_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg(v_ref_1101_, v_constName_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v_ref_1101_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2___redArg(lean_object* v_constName_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_ref_1111_; lean_object* v___x_1112_; 
v_ref_1111_ = lean_ctor_get(v___y_1108_, 5);
v___x_1112_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg(v_ref_1111_, v_constName_1107_, v___y_1108_, v___y_1109_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2___redArg(v_constName_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1(lean_object* v_constName_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1122_; lean_object* v_env_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; 
v___x_1122_ = lean_st_ref_get(v___y_1120_);
v_env_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc_ref(v_env_1123_);
lean_dec(v___x_1122_);
v___x_1124_ = 0;
lean_inc(v_constName_1118_);
v___x_1125_ = l_Lean_Environment_find_x3f(v_env_1123_, v_constName_1118_, v___x_1124_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2___redArg(v_constName_1118_, v___y_1119_, v___y_1120_);
return v___x_1126_;
}
else
{
lean_object* v_val_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_constName_1118_);
v_val_1127_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1125_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_val_1127_);
lean_dec(v___x_1125_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set_tag(v___x_1129_, 0);
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_val_1127_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1___boxed(lean_object* v_constName_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1(v_constName_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isCtorOverride_x3f(lean_object* v_declName_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v_env_1145_; lean_object* v___x_1146_; 
v___x_1144_ = lean_st_ref_get(v_a_1142_);
v_env_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc_ref(v_env_1145_);
lean_dec(v___x_1144_);
lean_inc(v_declName_1140_);
v___x_1146_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_1145_, v_declName_1140_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_isCtor_x3f___at___00Lean_Compiler_isCtorOverride_x3f_spec__0(v_declName_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1168_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1168_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1168_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
if (lean_obj_tag(v_a_1148_) == 1)
{
lean_object* v_val_1152_; lean_object* v___x_1153_; lean_object* v_env_1154_; lean_object* v_induct_1155_; uint8_t v___x_1156_; 
v_val_1152_ = lean_ctor_get(v_a_1148_, 0);
v___x_1153_ = lean_st_ref_get(v_a_1142_);
v_env_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc_ref(v_env_1154_);
lean_dec(v___x_1153_);
v_induct_1155_ = lean_ctor_get(v_val_1152_, 1);
lean_inc(v_induct_1155_);
v___x_1156_ = l_Lean_Compiler_hasInductiveOverride(v_env_1154_, v_induct_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1158_; 
if (v_isShared_1151_ == 0)
{
v___x_1158_ = v___x_1150_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1148_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
lean_dec_ref_known(v_a_1148_, 1);
v___x_1160_ = lean_box(0);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1160_);
v___x_1162_ = v___x_1150_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_dec(v_a_1148_);
v___x_1164_ = lean_box(0);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1164_);
v___x_1166_ = v___x_1150_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
else
{
return v___x_1147_;
}
}
else
{
lean_object* v_val_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1203_; 
v_val_1169_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1171_ = v___x_1146_;
v_isShared_1172_ = v_isSharedCheck_1203_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_val_1169_);
lean_dec(v___x_1146_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1203_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
if (lean_obj_tag(v_val_1169_) == 2)
{
lean_object* v_info_1173_; lean_object* v_induct_1174_; lean_object* v_cidx_1175_; lean_object* v_numParams_1176_; lean_object* v_numFields_1177_; lean_object* v___x_1178_; 
v_info_1173_ = lean_ctor_get(v_val_1169_, 1);
lean_inc_ref(v_info_1173_);
lean_dec_ref_known(v_val_1169_, 2);
v_induct_1174_ = lean_ctor_get(v_info_1173_, 0);
lean_inc(v_induct_1174_);
v_cidx_1175_ = lean_ctor_get(v_info_1173_, 1);
lean_inc(v_cidx_1175_);
v_numParams_1176_ = lean_ctor_get(v_info_1173_, 2);
lean_inc(v_numParams_1176_);
v_numFields_1177_ = lean_ctor_get(v_info_1173_, 3);
lean_inc(v_numFields_1177_);
lean_dec_ref(v_info_1173_);
v___x_1178_ = l_Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1(v_declName_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1192_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1192_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1192_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; uint8_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1183_ = l_Lean_ConstantInfo_toConstantVal(v_a_1179_);
v___x_1184_ = l_Lean_ConstantInfo_isUnsafe(v_a_1179_);
lean_dec(v_a_1179_);
v___x_1185_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v_induct_1174_);
lean_ctor_set(v___x_1185_, 2, v_cidx_1175_);
lean_ctor_set(v___x_1185_, 3, v_numParams_1176_);
lean_ctor_set(v___x_1185_, 4, v_numFields_1177_);
lean_ctor_set_uint8(v___x_1185_, sizeof(void*)*5, v___x_1184_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1185_);
v___x_1187_ = v___x_1171_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1187_);
v___x_1189_ = v___x_1181_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
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
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_numFields_1177_);
lean_dec(v_numParams_1176_);
lean_dec(v_cidx_1175_);
lean_dec(v_induct_1174_);
lean_del_object(v___x_1171_);
v_a_1193_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1178_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1178_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_del_object(v___x_1171_);
lean_dec(v_val_1169_);
lean_dec(v_declName_1140_);
v___x_1201_ = lean_box(0);
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isCtorOverride_x3f___boxed(lean_object* v_declName_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Compiler_isCtorOverride_x3f(v_declName_1204_, v_a_1205_, v_a_1206_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1209_, lean_object* v_constName_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2___redArg(v_constName_1210_, v___y_1211_, v___y_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1215_, lean_object* v_constName_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2(v_00_u03b1_1215_, v_constName_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_1221_, lean_object* v_ref_1222_, lean_object* v_constName_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg(v_ref_1222_, v_constName_1223_, v___y_1224_, v___y_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1228_, lean_object* v_ref_1229_, lean_object* v_constName_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3(v_00_u03b1_1228_, v_ref_1229_, v_constName_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v_ref_1229_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1235_, lean_object* v_ref_1236_, lean_object* v_msg_1237_, lean_object* v_declHint_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1236_, v_msg_1237_, v_declHint_1238_, v___y_1239_, v___y_1240_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1243_, lean_object* v_ref_1244_, lean_object* v_msg_1245_, lean_object* v_declHint_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_1243_, v_ref_1244_, v_msg_1245_, v_declHint_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v_ref_1244_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_1251_, lean_object* v_declHint_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1251_, v_declHint_1252_, v___y_1254_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1257_, lean_object* v_declHint_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(v_msg_1257_, v_declHint_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_1263_, lean_object* v_ref_1264_, lean_object* v_msg_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1264_, v_msg_1265_, v___y_1266_, v___y_1267_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1270_, lean_object* v_ref_1271_, lean_object* v_msg_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6(v_00_u03b1_1270_, v_ref_1271_, v_msg_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v_ref_1271_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1277_, lean_object* v_msg_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_1278_, v___y_1279_, v___y_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_msg_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(v_00_u03b1_1283_, v_msg_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
return v_res_1288_;
}
}
static lean_object* _init_l_Lean_Compiler_getConstInfoCtorOverride___closed__1(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l_Lean_Compiler_getConstInfoCtorOverride___closed__0));
v___x_1291_ = l_Lean_stringToMessageData(v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getConstInfoCtorOverride(lean_object* v_declName_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v___x_1296_; 
lean_inc(v_declName_1292_);
v___x_1296_ = l_Lean_Compiler_isCtorOverride_x3f(v_declName_1292_, v_a_1293_, v_a_1294_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1312_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1312_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1312_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
if (lean_obj_tag(v_a_1297_) == 0)
{
lean_object* v___x_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_del_object(v___x_1299_);
v___x_1301_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3___redArg___closed__2);
v___x_1302_ = 0;
v___x_1303_ = l_Lean_MessageData_ofConstName(v_declName_1292_, v___x_1302_);
v___x_1304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1301_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = lean_obj_once(&l_Lean_Compiler_getConstInfoCtorOverride___closed__1, &l_Lean_Compiler_getConstInfoCtorOverride___closed__1_once, _init_l_Lean_Compiler_getConstInfoCtorOverride___closed__1);
v___x_1306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_isCtorOverride_x3f_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v___x_1306_, v_a_1293_, v_a_1294_);
return v___x_1307_;
}
else
{
lean_object* v_val_1308_; lean_object* v___x_1310_; 
lean_dec(v_declName_1292_);
v_val_1308_ = lean_ctor_get(v_a_1297_, 0);
lean_inc(v_val_1308_);
lean_dec_ref_known(v_a_1297_, 1);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v_val_1308_);
v___x_1310_ = v___x_1299_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_val_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec(v_declName_1292_);
v_a_1313_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1296_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1296_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getConstInfoCtorOverride___boxed(lean_object* v_declName_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_Compiler_getConstInfoCtorOverride(v_declName_1321_, v_a_1322_, v_a_1323_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverrideSimpleCore_x3f(lean_object* v_env_1326_, lean_object* v_declName_1327_){
_start:
{
lean_object* v___x_1328_; 
lean_inc(v_declName_1327_);
lean_inc_ref(v_env_1326_);
v___x_1328_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_1326_, v_declName_1327_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_isInductiveCore_x3f(v_env_1326_, v_declName_1327_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_box(0);
return v___x_1330_;
}
else
{
lean_object* v_val_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1342_; 
v_val_1331_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1333_ = v___x_1329_;
v_isShared_1334_ = v_isSharedCheck_1342_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_val_1331_);
lean_dec(v___x_1329_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1342_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_numParams_1335_; lean_object* v_ctors_1336_; uint8_t v_isRec_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v_numParams_1335_ = lean_ctor_get(v_val_1331_, 1);
lean_inc(v_numParams_1335_);
v_ctors_1336_ = lean_ctor_get(v_val_1331_, 4);
lean_inc(v_ctors_1336_);
v_isRec_1337_ = lean_ctor_get_uint8(v_val_1331_, sizeof(void*)*6);
lean_dec(v_val_1331_);
v___x_1338_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1338_, 0, v_numParams_1335_);
lean_ctor_set(v___x_1338_, 1, v_ctors_1336_);
lean_ctor_set_uint8(v___x_1338_, sizeof(void*)*2, v_isRec_1337_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1338_);
v___x_1340_ = v___x_1333_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
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
else
{
lean_object* v_val_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1352_; 
lean_dec(v_declName_1327_);
lean_dec_ref(v_env_1326_);
v_val_1343_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1345_ = v___x_1328_;
v_isShared_1346_ = v_isSharedCheck_1352_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_val_1343_);
lean_dec(v___x_1328_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1352_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
if (lean_obj_tag(v_val_1343_) == 1)
{
lean_object* v_info_1347_; lean_object* v___x_1349_; 
v_info_1347_ = lean_ctor_get(v_val_1343_, 1);
lean_inc_ref(v_info_1347_);
lean_dec_ref_known(v_val_1343_, 2);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v_info_1347_);
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_info_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
else
{
lean_object* v___x_1351_; 
lean_del_object(v___x_1345_);
lean_dec(v_val_1343_);
v___x_1351_ = lean_box(0);
return v___x_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverride___redArg(lean_object* v_declName_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; lean_object* v_env_1357_; lean_object* v___x_1358_; 
v___x_1356_ = lean_st_ref_get(v_a_1354_);
v_env_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc_ref(v_env_1357_);
lean_dec(v___x_1356_);
v___x_1358_ = l_Lean_Compiler_isInductiveOverrideSimpleCore_x3f(v_env_1357_, v_declName_1353_);
if (lean_obj_tag(v___x_1358_) == 0)
{
uint8_t v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = 0;
v___x_1360_ = lean_box(v___x_1359_);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
else
{
lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1370_; 
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; 
v_unused_1371_ = lean_ctor_get(v___x_1358_, 0);
lean_dec(v_unused_1371_);
v___x_1363_ = v___x_1358_;
v_isShared_1364_ = v_isSharedCheck_1370_;
goto v_resetjp_1362_;
}
else
{
lean_dec(v___x_1358_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1370_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
uint8_t v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1365_ = 1;
v___x_1366_ = lean_box(v___x_1365_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set_tag(v___x_1363_, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1366_);
v___x_1368_ = v___x_1363_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverride___redArg___boxed(lean_object* v_declName_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_Compiler_isInductiveOverride___redArg(v_declName_1372_, v_a_1373_);
lean_dec(v_a_1373_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverride(lean_object* v_declName_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v___x_1380_; lean_object* v_env_1381_; lean_object* v___x_1382_; 
v___x_1380_ = lean_st_ref_get(v_a_1378_);
v_env_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc_ref(v_env_1381_);
lean_dec(v___x_1380_);
v___x_1382_ = l_Lean_Compiler_isInductiveOverrideSimpleCore_x3f(v_env_1381_, v_declName_1376_);
if (lean_obj_tag(v___x_1382_) == 0)
{
uint8_t v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = 0;
v___x_1384_ = lean_box(v___x_1383_);
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
return v___x_1385_;
}
else
{
lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1394_; 
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1394_ == 0)
{
lean_object* v_unused_1395_; 
v_unused_1395_ = lean_ctor_get(v___x_1382_, 0);
lean_dec(v_unused_1395_);
v___x_1387_ = v___x_1382_;
v_isShared_1388_ = v_isSharedCheck_1394_;
goto v_resetjp_1386_;
}
else
{
lean_dec(v___x_1382_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1394_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
uint8_t v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1389_ = 1;
v___x_1390_ = lean_box(v___x_1389_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set_tag(v___x_1387_, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1390_);
v___x_1392_ = v___x_1387_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverride___boxed(lean_object* v_declName_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Compiler_isInductiveOverride(v_declName_1396_, v_a_1397_, v_a_1398_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverrideSimple_x3f___redArg(lean_object* v_declName_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v_env_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1404_ = lean_st_ref_get(v_a_1402_);
v_env_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc_ref(v_env_1405_);
lean_dec(v___x_1404_);
v___x_1406_ = l_Lean_Compiler_isInductiveOverrideSimpleCore_x3f(v_env_1405_, v_declName_1401_);
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverrideSimple_x3f___redArg___boxed(lean_object* v_declName_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_Compiler_isInductiveOverrideSimple_x3f___redArg(v_declName_1408_, v_a_1409_);
lean_dec(v_a_1409_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverrideSimple_x3f(lean_object* v_declName_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v___x_1416_; lean_object* v_env_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1416_ = lean_st_ref_get(v_a_1414_);
v_env_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc_ref(v_env_1417_);
lean_dec(v___x_1416_);
v___x_1418_ = l_Lean_Compiler_isInductiveOverrideSimpleCore_x3f(v_env_1417_, v_declName_1412_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isInductiveOverrideSimple_x3f___boxed(lean_object* v_declName_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_Compiler_isInductiveOverrideSimple_x3f(v_declName_1420_, v_a_1421_, v_a_1422_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Compiler_isCompilerRelevantType_spec__0___redArg(lean_object* v_declName_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___x_1428_; lean_object* v_env_1429_; uint8_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1428_ = lean_st_ref_get(v___y_1426_);
v_env_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc_ref(v_env_1429_);
lean_dec(v___x_1428_);
v___x_1430_ = l_Lean_isInductiveCore(v_env_1429_, v_declName_1425_);
v___x_1431_ = lean_box(v___x_1430_);
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Compiler_isCompilerRelevantType_spec__0___redArg___boxed(lean_object* v_declName_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_isInductive___at___00Lean_Compiler_isCompilerRelevantType_spec__0___redArg(v_declName_1433_, v___y_1434_);
lean_dec(v___y_1434_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Compiler_isCompilerRelevantType_spec__0(lean_object* v_declName_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_isInductive___at___00Lean_Compiler_isCompilerRelevantType_spec__0___redArg(v_declName_1437_, v___y_1439_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Compiler_isCompilerRelevantType_spec__0___boxed(lean_object* v_declName_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_isInductive___at___00Lean_Compiler_isCompilerRelevantType_spec__0(v_declName_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isCompilerRelevantType(lean_object* v_declName_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v___x_1451_; lean_object* v_env_1452_; lean_object* v___x_1453_; 
v___x_1451_ = lean_st_ref_get(v_a_1449_);
v_env_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc_ref(v_env_1452_);
lean_dec(v___x_1451_);
lean_inc(v_declName_1447_);
v___x_1453_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_1452_, v_declName_1447_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_isInductive___at___00Lean_Compiler_isCompilerRelevantType_spec__0___redArg(v_declName_1447_, v_a_1449_);
return v___x_1454_;
}
else
{
lean_object* v_val_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_declName_1447_);
v_val_1455_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1457_ = v___x_1453_;
v_isShared_1458_ = v_isSharedCheck_1474_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_val_1455_);
lean_dec(v___x_1453_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1474_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
switch(lean_obj_tag(v_val_1455_))
{
case 1:
{
uint8_t v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_dec_ref_known(v_val_1455_, 2);
v___x_1459_ = 1;
v___x_1460_ = lean_box(v___x_1459_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set_tag(v___x_1457_, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1460_);
v___x_1462_ = v___x_1457_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
case 0:
{
uint8_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_dec_ref_known(v_val_1455_, 2);
v___x_1464_ = 1;
v___x_1465_ = lean_box(v___x_1464_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set_tag(v___x_1457_, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1465_);
v___x_1467_ = v___x_1457_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
default: 
{
uint8_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1472_; 
lean_dec(v_val_1455_);
v___x_1469_ = 0;
v___x_1470_ = lean_box(v___x_1469_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set_tag(v___x_1457_, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1470_);
v___x_1472_ = v___x_1457_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isCompilerRelevantType___boxed(lean_object* v_declName_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Compiler_isCompilerRelevantType(v_declName_1475_, v_a_1476_, v_a_1477_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
return v_res_1479_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Compiler_hasNoncomputableOverride_spec__0(lean_object* v_msg_1480_){
_start:
{
lean_object* v___f_1481_; lean_object* v___f_1482_; lean_object* v___f_1483_; lean_object* v___f_1484_; lean_object* v___f_1485_; lean_object* v___f_1486_; lean_object* v___f_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___f_1481_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__0));
v___f_1482_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__1));
v___f_1483_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__2));
v___f_1484_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__3));
v___f_1485_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__4));
v___f_1486_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__5));
v___f_1487_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct_spec__0___closed__6));
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___f_1481_);
lean_ctor_set(v___x_1488_, 1, v___f_1482_);
v___x_1489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v___f_1483_);
lean_ctor_set(v___x_1489_, 2, v___f_1484_);
lean_ctor_set(v___x_1489_, 3, v___f_1485_);
lean_ctor_set(v___x_1489_, 4, v___f_1486_);
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
lean_ctor_set(v___x_1490_, 1, v___f_1487_);
v___x_1491_ = 0;
v___x_1492_ = lean_box(v___x_1491_);
v___x_1493_ = l_instInhabitedOfMonad___redArg(v___x_1490_, v___x_1492_);
v___x_1494_ = lean_panic_fn_borrowed(v___x_1493_, v_msg_1480_);
lean_dec(v___x_1493_);
v___x_1495_ = lean_unbox(v___x_1494_);
lean_dec(v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_hasNoncomputableOverride_spec__0___boxed(lean_object* v_msg_1496_){
_start:
{
uint8_t v_res_1497_; lean_object* v_r_1498_; 
v_res_1497_ = l_panic___at___00Lean_Compiler_hasNoncomputableOverride_spec__0(v_msg_1496_);
v_r_1498_ = lean_box(v_res_1497_);
return v_r_1498_;
}
}
static lean_object* _init_l_Lean_Compiler_hasNoncomputableOverride___closed__1(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1500_ = ((lean_object*)(l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct___closed__1));
v___x_1501_ = lean_unsigned_to_nat(45u);
v___x_1502_ = lean_unsigned_to_nat(245u);
v___x_1503_ = ((lean_object*)(l_Lean_Compiler_hasNoncomputableOverride___closed__0));
v___x_1504_ = ((lean_object*)(l_Lean_Compiler_addInductiveOverride___closed__2));
v___x_1505_ = l_mkPanicMessageWithDecl(v___x_1504_, v___x_1503_, v___x_1502_, v___x_1501_, v___x_1500_);
return v___x_1505_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasNoncomputableOverride(lean_object* v_env_1506_, lean_object* v_declName_1507_){
_start:
{
uint8_t v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = 0;
lean_inc(v_declName_1507_);
lean_inc_ref(v_env_1506_);
v___x_1509_ = l_Lean_Environment_findAsync_x3f(v_env_1506_, v_declName_1507_, v___x_1508_);
if (lean_obj_tag(v___x_1509_) == 1)
{
lean_object* v_val_1510_; uint8_t v_kind_1511_; 
v_val_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_val_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v_kind_1511_ = lean_ctor_get_uint8(v_val_1510_, sizeof(void*)*3);
switch(v_kind_1511_)
{
case 6:
{
lean_object* v___x_1512_; 
lean_dec(v_declName_1507_);
v___x_1512_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1510_);
if (lean_obj_tag(v___x_1512_) == 6)
{
lean_object* v_val_1513_; lean_object* v_induct_1514_; uint8_t v___x_1515_; 
v_val_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc_ref(v_val_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v_induct_1514_ = lean_ctor_get(v_val_1513_, 1);
lean_inc(v_induct_1514_);
lean_dec_ref(v_val_1513_);
v___x_1515_ = l_Lean_Compiler_hasInductiveOverride(v_env_1506_, v_induct_1514_);
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; uint8_t v___x_1517_; 
lean_dec_ref(v___x_1512_);
lean_dec_ref(v_env_1506_);
v___x_1516_ = lean_obj_once(&l_Lean_Compiler_hasNoncomputableOverride___closed__1, &l_Lean_Compiler_hasNoncomputableOverride___closed__1_once, _init_l_Lean_Compiler_hasNoncomputableOverride___closed__1);
v___x_1517_ = l_panic___at___00Lean_Compiler_hasNoncomputableOverride_spec__0(v___x_1516_);
return v___x_1517_;
}
}
case 0:
{
uint8_t v___x_1518_; 
lean_inc(v_declName_1507_);
lean_inc_ref(v_env_1506_);
v___x_1518_ = l_Lean_isCasesOnRecursor(v_env_1506_, v_declName_1507_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; 
lean_dec(v_val_1510_);
lean_inc_ref(v_env_1506_);
v___x_1519_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1506_, v_declName_1507_);
if (lean_obj_tag(v___x_1519_) == 1)
{
lean_object* v_val_1520_; lean_object* v_ctorName_1521_; lean_object* v___x_1522_; 
v_val_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_val_1520_);
lean_dec_ref_known(v___x_1519_, 1);
v_ctorName_1521_ = lean_ctor_get(v_val_1520_, 0);
lean_inc(v_ctorName_1521_);
lean_dec(v_val_1520_);
lean_inc_ref(v_env_1506_);
v___x_1522_ = l_Lean_Environment_find_x3f(v_env_1506_, v_ctorName_1521_, v___x_1518_);
if (lean_obj_tag(v___x_1522_) == 1)
{
lean_object* v_val_1523_; 
v_val_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_val_1523_);
lean_dec_ref_known(v___x_1522_, 1);
if (lean_obj_tag(v_val_1523_) == 6)
{
lean_object* v_val_1524_; lean_object* v_induct_1525_; uint8_t v___x_1526_; 
v_val_1524_ = lean_ctor_get(v_val_1523_, 0);
lean_inc_ref(v_val_1524_);
lean_dec_ref_known(v_val_1523_, 1);
v_induct_1525_ = lean_ctor_get(v_val_1524_, 1);
lean_inc(v_induct_1525_);
lean_dec_ref(v_val_1524_);
v___x_1526_ = l_Lean_Compiler_hasInductiveOverride(v_env_1506_, v_induct_1525_);
return v___x_1526_;
}
else
{
lean_dec(v_val_1523_);
lean_dec_ref(v_env_1506_);
return v___x_1518_;
}
}
else
{
lean_dec(v___x_1522_);
lean_dec_ref(v_env_1506_);
return v___x_1518_;
}
}
else
{
lean_dec(v___x_1519_);
lean_dec_ref(v_env_1506_);
return v___x_1518_;
}
}
else
{
lean_object* v___x_1527_; lean_object* v_type_1528_; lean_object* v_indTypeName_1529_; uint8_t v___x_1530_; 
lean_dec(v_declName_1507_);
v___x_1527_ = l_Lean_AsyncConstantInfo_toConstantVal(v_val_1510_);
v_type_1528_ = lean_ctor_get(v___x_1527_, 2);
lean_inc_ref(v_type_1528_);
lean_dec_ref(v___x_1527_);
v_indTypeName_1529_ = l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_casesEliminatorInduct(v_type_1528_);
lean_inc(v_indTypeName_1529_);
lean_inc_ref(v_env_1506_);
v___x_1530_ = l_Lean_Compiler_hasInductiveOverride(v_env_1506_, v_indTypeName_1529_);
if (v___x_1530_ == 0)
{
lean_dec(v_indTypeName_1529_);
lean_dec_ref(v_env_1506_);
return v___x_1530_;
}
else
{
uint8_t v___x_1531_; 
v___x_1531_ = l_Lean_isStructure(v_env_1506_, v_indTypeName_1529_);
if (v___x_1531_ == 0)
{
return v___x_1530_;
}
else
{
return v___x_1508_;
}
}
}
}
default: 
{
lean_dec(v_val_1510_);
lean_dec(v_declName_1507_);
lean_dec_ref(v_env_1506_);
return v___x_1508_;
}
}
}
else
{
lean_dec(v___x_1509_);
lean_dec(v_declName_1507_);
lean_dec_ref(v_env_1506_);
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasNoncomputableOverride___boxed(lean_object* v_env_1532_, lean_object* v_declName_1533_){
_start:
{
uint8_t v_res_1534_; lean_object* v_r_1535_; 
v_res_1534_ = l_Lean_Compiler_hasNoncomputableOverride(v_env_1532_, v_declName_1533_);
v_r_1535_ = lean_box(v_res_1534_);
return v_r_1535_;
}
}
lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CasesInfo(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_InductiveOverride(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CasesInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_instInhabitedInductiveOverride_default = _init_l_Lean_Compiler_instInhabitedInductiveOverride_default();
lean_mark_persistent(l_Lean_Compiler_instInhabitedInductiveOverride_default);
l_Lean_Compiler_instInhabitedInductiveOverride = _init_l_Lean_Compiler_instInhabitedInductiveOverride();
lean_mark_persistent(l_Lean_Compiler_instInhabitedInductiveOverride);
res = l___private_Lean_Compiler_InductiveOverride_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InductiveOverride_1521490206____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_inductiveOverrideExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_inductiveOverrideExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_InductiveOverride(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_ProjFns(uint8_t builtin);
lean_object* initialize_Lean_Structure(uint8_t builtin);
lean_object* initialize_Lean_Meta_CasesInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_InductiveOverride(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CasesInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_InductiveOverride(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_InductiveOverride(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_InductiveOverride(builtin);
}
#ifdef __cplusplus
}
#endif
