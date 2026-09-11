// Lean compiler output
// Module: Lean.Compiler.LCNF.ToImpureType
// Imports: public import Lean.Compiler.LCNF.Irrelevant import Lean.Compiler.LCNF.MonoTypes import Init.Data.Format.Macro
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Irrelevant_setHasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCtorInfo_default;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclBaseType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Compiler_LCNF_getParamTypes(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CtorInfo_checkValid(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tagged"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 57, 252, 162, 142, 133, 51, 193)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__7_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__10_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ToImpureType"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 154, 3, 9, 42, 52, 199, 231)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(14, 103, 172, 122, 112, 104, 83, 202)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(183, 21, 192, 83, 126, 85, 186, 68)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 76, 182, 201, 28, 76, 239, 149)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(172, 159, 124, 100, 112, 3, 128, 86)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "impureTypeExt"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(123, 215, 204, 232, 104, 251, 181, 107)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "impureTrivialStructureInfoExt"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(121, 218, 151, 106, 231, 134, 17, 84)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Subtype"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Void"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nonemptyType"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Float"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Float32"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lcErased"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lcVoid"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(68, 180, 59, 167, 252, 217, 37, 174)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__7_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(25, 168, 138, 20, 203, 141, 233, 12)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__11_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(171, 218, 234, 194, 194, 57, 75, 5)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__14 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__14_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(246, 232, 182, 48, 64, 193, 160, 231)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__17 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__17_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 69, 114, 85, 163, 177, 220, 67)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__20 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__20_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__23 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__23_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__26 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__26_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___boxed(lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Compiler.LCNF.ToImpureType"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.computeImpureType"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__3;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__5;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__6;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__9;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__11;
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__12 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__12_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__14;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__15;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__16;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "obj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 235, 44, 74, 242, 121, 239, 90)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_setImpureType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_setImpureType___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_setImpureType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_setImpureType___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_setImpureType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_setImpureType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setImpureType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setImpureType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_nameToImpureType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Compiler_LCNF_nameToImpureType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_nameToImpureType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_nameToImpureType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_nameToImpureType___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_nameToImpureType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "` was not compiled; `compileDecls` must run on inductive types first"};
static const lean_object* l_Lean_Compiler_LCNF_nameToImpureType___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_nameToImpureType___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_nameToImpureType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_nameToImpureType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_nameToImpureType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_nameToImpureType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lcAny"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_toImpureType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_toImpureType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_toImpureType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toImpureType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toImpureType___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_toImpureType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Compiler.LCNF.toImpureType"};
static const lean_object* l_Lean_Compiler_LCNF_toImpureType___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_toImpureType___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toImpureType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toImpureType___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_toImpureType___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toImpureType___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpureType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpureType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_erased_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_erased_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_object_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_object_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_usize_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_usize_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_scalar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_scalar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_void_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_void_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "◾"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "obj@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__2_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__4_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "usize@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__6_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "scalar#"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__8_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__8_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__10_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__10_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__11_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "void"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__12_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__12_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format(lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat___closed__0_value;
static const lean_array_object l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCtorLayout;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ctorLayoutExt"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 123, 250, 80, 124, 9, 225, 155)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.setCtorLayout.fillCache"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setCtorLayout(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setCtorLayout___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getCtorLayout(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getCtorLayout___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Compiler.LCNF.compileInductives"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_compileInductives___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_compileInductives___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_compileInductives___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compileInductives(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compileInductives___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = lean_box(0);
v___x_11_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__4));
v___x_12_ = l_Lean_Expr_const___override(v___x_11_, v___x_10_);
return v___x_12_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = lean_box(0);
v___x_17_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__7));
v___x_18_ = l_Lean_Expr_const___override(v___x_17_, v___x_16_);
return v___x_18_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_box(0);
v___x_23_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__10));
v___x_24_ = l_Lean_Expr_const___override(v___x_23_, v___x_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum(lean_object* v_numCtors_25_){
_start:
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_dec_eq(v_numCtors_25_, v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_28_ = lean_unsigned_to_nat(256u);
v___x_29_ = lean_nat_dec_lt(v_numCtors_25_, v___x_28_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(65536u);
v___x_31_ = lean_nat_dec_lt(v_numCtors_25_, v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_cstr_to_nat("4294967296");
v___x_33_ = lean_nat_dec_lt(v_numCtors_25_, v___x_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
v___x_34_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2);
return v___x_34_;
}
else
{
lean_object* v___x_35_; 
v___x_35_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5);
return v___x_35_;
}
}
else
{
lean_object* v___x_36_; 
v___x_36_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8);
return v___x_36_;
}
}
else
{
lean_object* v___x_37_; 
v___x_37_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11);
return v___x_37_;
}
}
else
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___boxed(lean_object* v_numCtors_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum(v_numCtors_39_);
lean_dec(v_numCtors_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_41_, lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v_k_43_; lean_object* v_v_44_; lean_object* v_l_45_; lean_object* v_r_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_k_43_ = lean_ctor_get(v_x_42_, 1);
v_v_44_ = lean_ctor_get(v_x_42_, 2);
v_l_45_ = lean_ctor_get(v_x_42_, 3);
v_r_46_ = lean_ctor_get(v_x_42_, 4);
v___x_47_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0_spec__0(v_init_41_, v_l_45_);
lean_inc(v_v_44_);
lean_inc(v_k_43_);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v_k_43_);
lean_ctor_set(v___x_48_, 1, v_v_44_);
v___x_49_ = lean_array_push(v___x_47_, v___x_48_);
v_init_41_ = v___x_49_;
v_x_42_ = v_r_46_;
goto _start;
}
else
{
return v_init_41_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_51_, lean_object* v_x_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0_spec__0(v_init_51_, v_x_52_);
lean_dec(v_x_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1(lean_object* v_env_54_, lean_object* v_as_55_, size_t v_i_56_, size_t v_stop_57_, lean_object* v_b_58_){
_start:
{
lean_object* v___y_60_; uint8_t v___x_64_; 
v___x_64_ = lean_usize_dec_eq(v_i_56_, v_stop_57_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v_fst_66_; uint8_t v___x_67_; 
v___x_65_ = lean_array_uget_borrowed(v_as_55_, v_i_56_);
v_fst_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_fst_66_);
lean_inc_ref(v_env_54_);
v___x_67_ = l_Lean_Environment_contains(v_env_54_, v_fst_66_, v___x_64_);
if (v___x_67_ == 0)
{
v___y_60_ = v_b_58_;
goto v___jp_59_;
}
else
{
lean_object* v___x_68_; 
lean_inc(v___x_65_);
v___x_68_ = lean_array_push(v_b_58_, v___x_65_);
v___y_60_ = v___x_68_;
goto v___jp_59_;
}
}
else
{
lean_dec_ref(v_env_54_);
return v_b_58_;
}
v___jp_59_:
{
size_t v___x_61_; size_t v___x_62_; 
v___x_61_ = ((size_t)1ULL);
v___x_62_ = lean_usize_add(v_i_56_, v___x_61_);
v_i_56_ = v___x_62_;
v_b_58_ = v___y_60_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_69_, lean_object* v_as_70_, lean_object* v_i_71_, lean_object* v_stop_72_, lean_object* v_b_73_){
_start:
{
size_t v_i_boxed_74_; size_t v_stop_boxed_75_; lean_object* v_res_76_; 
v_i_boxed_74_ = lean_unbox_usize(v_i_71_);
lean_dec(v_i_71_);
v_stop_boxed_75_ = lean_unbox_usize(v_stop_72_);
lean_dec(v_stop_72_);
v_res_76_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1(v_env_69_, v_as_70_, v_i_boxed_74_, v_stop_boxed_75_, v_b_73_);
lean_dec_ref(v_as_70_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_(lean_object* v___x_77_, lean_object* v_env_78_, lean_object* v_s_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_80_ = lean_mk_empty_array_with_capacity(v___x_77_);
v___x_81_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0_spec__0(v___x_80_, v_s_79_);
v___x_82_ = lean_array_get_size(v___x_81_);
v___x_83_ = lean_mk_empty_array_with_capacity(v___x_77_);
v___x_84_ = lean_nat_dec_lt(v___x_77_, v___x_82_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
lean_dec_ref(v___x_81_);
lean_dec_ref(v_env_78_);
lean_inc_ref_n(v___x_83_, 2);
v___x_85_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_83_);
lean_ctor_set(v___x_85_, 2, v___x_83_);
return v___x_85_;
}
else
{
uint8_t v___x_86_; 
v___x_86_ = lean_nat_dec_le(v___x_82_, v___x_82_);
if (v___x_86_ == 0)
{
if (v___x_84_ == 0)
{
lean_object* v___x_87_; 
lean_dec_ref(v___x_81_);
lean_dec_ref(v_env_78_);
lean_inc_ref_n(v___x_83_, 2);
v___x_87_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_87_, 0, v___x_83_);
lean_ctor_set(v___x_87_, 1, v___x_83_);
lean_ctor_set(v___x_87_, 2, v___x_83_);
return v___x_87_;
}
else
{
size_t v___x_88_; size_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = ((size_t)0ULL);
v___x_89_ = lean_usize_of_nat(v___x_82_);
v___x_90_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1(v_env_78_, v___x_81_, v___x_88_, v___x_89_, v___x_83_);
lean_dec_ref(v___x_81_);
lean_inc_ref_n(v___x_90_, 2);
v___x_91_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
lean_ctor_set(v___x_91_, 2, v___x_90_);
return v___x_91_;
}
}
else
{
size_t v___x_92_; size_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = ((size_t)0ULL);
v___x_93_ = lean_usize_of_nat(v___x_82_);
v___x_94_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1(v_env_78_, v___x_81_, v___x_92_, v___x_93_, v___x_83_);
lean_dec_ref(v___x_81_);
lean_inc_ref_n(v___x_94_, 2);
v___x_95_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
lean_ctor_set(v___x_95_, 2, v___x_94_);
return v___x_95_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2____boxed(lean_object* v___x_96_, lean_object* v_env_97_, lean_object* v_s_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_(v___x_96_, v_env_97_, v_s_98_);
lean_dec(v_s_98_);
lean_dec(v___x_96_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___f_139_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_));
v___x_140_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_));
v___x_141_ = lean_box(0);
v___x_142_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_140_, v___x_141_, v___f_139_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2____boxed(lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_();
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0(lean_object* v_init_145_, lean_object* v_t_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0_spec__0(v_init_145_, v_t_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_148_, lean_object* v_t_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0(v_init_148_, v_t_149_);
lean_dec(v_t_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_object* v_k_153_; lean_object* v_v_154_; lean_object* v_l_155_; lean_object* v_r_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_k_153_ = lean_ctor_get(v_x_152_, 1);
v_v_154_ = lean_ctor_get(v_x_152_, 2);
v_l_155_ = lean_ctor_get(v_x_152_, 3);
v_r_156_ = lean_ctor_get(v_x_152_, 4);
v___x_157_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0_spec__0(v_init_151_, v_l_155_);
lean_inc(v_v_154_);
lean_inc(v_k_153_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v_k_153_);
lean_ctor_set(v___x_158_, 1, v_v_154_);
v___x_159_ = lean_array_push(v___x_157_, v___x_158_);
v_init_151_ = v___x_159_;
v_x_152_ = v_r_156_;
goto _start;
}
else
{
return v_init_151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_161_, lean_object* v_x_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0_spec__0(v_init_161_, v_x_162_);
lean_dec(v_x_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1(lean_object* v_env_164_, lean_object* v_as_165_, size_t v_i_166_, size_t v_stop_167_, lean_object* v_b_168_){
_start:
{
lean_object* v___y_170_; uint8_t v___x_174_; 
v___x_174_ = lean_usize_dec_eq(v_i_166_, v_stop_167_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v_fst_176_; uint8_t v___x_177_; 
v___x_175_ = lean_array_uget_borrowed(v_as_165_, v_i_166_);
v_fst_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_fst_176_);
lean_inc_ref(v_env_164_);
v___x_177_ = l_Lean_Environment_contains(v_env_164_, v_fst_176_, v___x_174_);
if (v___x_177_ == 0)
{
v___y_170_ = v_b_168_;
goto v___jp_169_;
}
else
{
lean_object* v___x_178_; 
lean_inc(v___x_175_);
v___x_178_ = lean_array_push(v_b_168_, v___x_175_);
v___y_170_ = v___x_178_;
goto v___jp_169_;
}
}
else
{
lean_dec_ref(v_env_164_);
return v_b_168_;
}
v___jp_169_:
{
size_t v___x_171_; size_t v___x_172_; 
v___x_171_ = ((size_t)1ULL);
v___x_172_ = lean_usize_add(v_i_166_, v___x_171_);
v_i_166_ = v___x_172_;
v_b_168_ = v___y_170_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_179_, lean_object* v_as_180_, lean_object* v_i_181_, lean_object* v_stop_182_, lean_object* v_b_183_){
_start:
{
size_t v_i_boxed_184_; size_t v_stop_boxed_185_; lean_object* v_res_186_; 
v_i_boxed_184_ = lean_unbox_usize(v_i_181_);
lean_dec(v_i_181_);
v_stop_boxed_185_ = lean_unbox_usize(v_stop_182_);
lean_dec(v_stop_182_);
v_res_186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1(v_env_179_, v_as_180_, v_i_boxed_184_, v_stop_boxed_185_, v_b_183_);
lean_dec_ref(v_as_180_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_(lean_object* v___x_187_, lean_object* v_env_188_, lean_object* v_s_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_190_ = lean_mk_empty_array_with_capacity(v___x_187_);
v___x_191_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0_spec__0(v___x_190_, v_s_189_);
v___x_192_ = lean_array_get_size(v___x_191_);
v___x_193_ = lean_mk_empty_array_with_capacity(v___x_187_);
v___x_194_ = lean_nat_dec_lt(v___x_187_, v___x_192_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_dec_ref(v___x_191_);
lean_dec_ref(v_env_188_);
lean_inc_ref_n(v___x_193_, 2);
v___x_195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_195_, 0, v___x_193_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
lean_ctor_set(v___x_195_, 2, v___x_193_);
return v___x_195_;
}
else
{
uint8_t v___x_196_; 
v___x_196_ = lean_nat_dec_le(v___x_192_, v___x_192_);
if (v___x_196_ == 0)
{
if (v___x_194_ == 0)
{
lean_object* v___x_197_; 
lean_dec_ref(v___x_191_);
lean_dec_ref(v_env_188_);
lean_inc_ref_n(v___x_193_, 2);
v___x_197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_197_, 0, v___x_193_);
lean_ctor_set(v___x_197_, 1, v___x_193_);
lean_ctor_set(v___x_197_, 2, v___x_193_);
return v___x_197_;
}
else
{
size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_198_ = ((size_t)0ULL);
v___x_199_ = lean_usize_of_nat(v___x_192_);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1(v_env_188_, v___x_191_, v___x_198_, v___x_199_, v___x_193_);
lean_dec_ref(v___x_191_);
lean_inc_ref_n(v___x_200_, 2);
v___x_201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
lean_ctor_set(v___x_201_, 2, v___x_200_);
return v___x_201_;
}
}
else
{
size_t v___x_202_; size_t v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_202_ = ((size_t)0ULL);
v___x_203_ = lean_usize_of_nat(v___x_192_);
v___x_204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1(v_env_188_, v___x_191_, v___x_202_, v___x_203_, v___x_193_);
lean_dec_ref(v___x_191_);
lean_inc_ref_n(v___x_204_, 2);
v___x_205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
lean_ctor_set(v___x_205_, 2, v___x_204_);
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2____boxed(lean_object* v___x_206_, lean_object* v_env_207_, lean_object* v_s_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_(v___x_206_, v_env_207_, v_s_208_);
lean_dec(v_s_208_);
lean_dec(v___x_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___f_217_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_));
v___x_218_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_));
v___x_219_ = lean_box(0);
v___x_220_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_218_, v___x_219_, v___f_217_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2____boxed(lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_();
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0(lean_object* v_init_223_, lean_object* v_t_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0_spec__0(v_init_223_, v_t_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_226_, lean_object* v_t_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0(v_init_226_, v_t_227_);
lean_dec(v_t_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType(lean_object* v_type_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___x_238_; 
lean_inc_ref(v_type_232_);
v___x_238_ = l_Lean_Meta_isProp(v_type_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; uint8_t v___x_240_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_a_239_);
v___x_240_ = lean_unbox(v_a_239_);
lean_dec(v_a_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
lean_dec_ref_known(v___x_238_, 1);
lean_inc_ref(v_type_232_);
v___x_241_ = l_Lean_Meta_isTypeFormerType(v_type_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; uint8_t v___x_243_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_a_242_);
v___x_243_ = lean_unbox(v_a_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; 
lean_dec_ref_known(v___x_241_, 1);
v___x_244_ = l_Lean_Meta_whnfD(v_type_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_314_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_314_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_314_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_314_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
if (lean_obj_tag(v_a_245_) == 11)
{
lean_object* v_typeName_249_; 
v_typeName_249_ = lean_ctor_get(v_a_245_, 0);
lean_inc(v_typeName_249_);
if (lean_obj_tag(v_typeName_249_) == 1)
{
lean_object* v_pre_250_; 
v_pre_250_ = lean_ctor_get(v_typeName_249_, 0);
if (lean_obj_tag(v_pre_250_) == 0)
{
lean_object* v_idx_251_; lean_object* v_struct_252_; lean_object* v_str_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_idx_251_ = lean_ctor_get(v_a_245_, 1);
lean_inc(v_idx_251_);
v_struct_252_ = lean_ctor_get(v_a_245_, 2);
lean_inc_ref(v_struct_252_);
lean_dec_ref_known(v_a_245_, 3);
v_str_253_ = lean_ctor_get(v_typeName_249_, 1);
lean_inc_ref(v_str_253_);
lean_dec_ref_known(v_typeName_249_, 2);
v___x_254_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__0));
v___x_255_ = lean_string_dec_eq(v_str_253_, v___x_254_);
lean_dec_ref(v_str_253_);
if (v___x_255_ == 0)
{
lean_object* v___x_257_; 
lean_dec_ref(v_struct_252_);
lean_dec(v_idx_251_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_257_ = v___x_247_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_242_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
else
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_nat_dec_eq(v_idx_251_, v___x_259_);
lean_dec(v_idx_251_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_263_; 
lean_dec_ref(v_struct_252_);
lean_dec(v_a_242_);
v___x_261_ = lean_box(v___x_260_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_261_);
v___x_263_ = v___x_247_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
else
{
if (lean_obj_tag(v_struct_252_) == 5)
{
lean_object* v_fn_265_; 
v_fn_265_ = lean_ctor_get(v_struct_252_, 0);
lean_inc_ref(v_fn_265_);
lean_dec_ref_known(v_struct_252_, 2);
if (lean_obj_tag(v_fn_265_) == 4)
{
lean_object* v_declName_266_; 
v_declName_266_ = lean_ctor_get(v_fn_265_, 0);
lean_inc(v_declName_266_);
if (lean_obj_tag(v_declName_266_) == 1)
{
lean_object* v_pre_267_; 
v_pre_267_ = lean_ctor_get(v_declName_266_, 0);
lean_inc(v_pre_267_);
if (lean_obj_tag(v_pre_267_) == 1)
{
lean_object* v_pre_268_; 
v_pre_268_ = lean_ctor_get(v_pre_267_, 0);
if (lean_obj_tag(v_pre_268_) == 0)
{
lean_object* v_us_269_; lean_object* v_str_270_; lean_object* v_str_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_us_269_ = lean_ctor_get(v_fn_265_, 1);
lean_inc(v_us_269_);
lean_dec_ref_known(v_fn_265_, 2);
v_str_270_ = lean_ctor_get(v_declName_266_, 1);
lean_inc_ref(v_str_270_);
lean_dec_ref_known(v_declName_266_, 2);
v_str_271_ = lean_ctor_get(v_pre_267_, 1);
lean_inc_ref(v_str_271_);
lean_dec_ref_known(v_pre_267_, 2);
v___x_272_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__1));
v___x_273_ = lean_string_dec_eq(v_str_271_, v___x_272_);
lean_dec_ref(v_str_271_);
if (v___x_273_ == 0)
{
lean_object* v___x_275_; 
lean_dec_ref(v_str_270_);
lean_dec(v_us_269_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_275_ = v___x_247_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_242_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
else
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__2));
v___x_278_ = lean_string_dec_eq(v_str_270_, v___x_277_);
lean_dec_ref(v_str_270_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_281_; 
lean_dec(v_us_269_);
lean_dec(v_a_242_);
v___x_279_ = lean_box(v___x_278_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_279_);
v___x_281_ = v___x_247_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
else
{
if (lean_obj_tag(v_us_269_) == 0)
{
lean_object* v___x_283_; lean_object* v___x_285_; 
lean_dec(v_a_242_);
v___x_283_ = lean_box(v___x_278_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_283_);
v___x_285_ = v___x_247_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
else
{
lean_object* v___x_288_; 
lean_dec(v_us_269_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_288_ = v___x_247_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_242_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
else
{
lean_object* v___x_291_; 
lean_dec_ref_known(v_pre_267_, 2);
lean_dec_ref_known(v_declName_266_, 2);
lean_dec_ref_known(v_fn_265_, 2);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_291_ = v___x_247_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_242_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
lean_object* v___x_294_; 
lean_dec(v_pre_267_);
lean_dec_ref_known(v_declName_266_, 2);
lean_dec_ref_known(v_fn_265_, 2);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_294_ = v___x_247_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_242_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_object* v___x_297_; 
lean_dec(v_declName_266_);
lean_dec_ref_known(v_fn_265_, 2);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_297_ = v___x_247_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_242_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
lean_object* v___x_300_; 
lean_dec_ref(v_fn_265_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_300_ = v___x_247_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_242_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
else
{
lean_object* v___x_303_; 
lean_dec_ref(v_struct_252_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_303_ = v___x_247_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_242_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
else
{
lean_object* v___x_306_; 
lean_dec_ref_known(v_typeName_249_, 2);
lean_dec_ref_known(v_a_245_, 3);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_306_ = v___x_247_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_242_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
else
{
lean_object* v___x_309_; 
lean_dec(v_typeName_249_);
lean_dec_ref_known(v_a_245_, 3);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_309_ = v___x_247_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_242_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
else
{
lean_object* v___x_312_; 
lean_dec(v_a_245_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_312_ = v___x_247_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_242_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec(v_a_242_);
v_a_315_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_244_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_244_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
else
{
lean_dec(v_a_242_);
lean_dec_ref(v_type_232_);
return v___x_241_;
}
}
else
{
lean_dec_ref(v_type_232_);
return v___x_241_;
}
}
else
{
lean_dec_ref(v_type_232_);
return v___x_238_;
}
}
else
{
lean_dec_ref(v_type_232_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___boxed(lean_object* v_type_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType(v_type_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f(lean_object* v_declName_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt;
v___x_336_ = ((lean_object*)(l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f___closed__0));
v___x_337_ = l_Lean_Compiler_LCNF_Irrelevant_setHasTrivialStructure_x3f(v___x_335_, v___x_336_, v_declName_331_, v_a_332_, v_a_333_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f___boxed(lean_object* v_declName_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f(v_declName_338_, v_a_339_, v_a_340_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(lean_object* v_declName_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt;
v___x_348_ = l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(v___x_347_, v_declName_343_, v_a_344_, v_a_345_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___boxed(lean_object* v_declName_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_declName_349_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
return v_res_353_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = lean_box(0);
v___x_364_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__7));
v___x_365_ = l_Lean_Expr_const___override(v___x_364_, v___x_363_);
return v___x_365_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8);
v___x_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_box(0);
v___x_372_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__11));
v___x_373_ = l_Lean_Expr_const___override(v___x_372_, v___x_371_);
return v___x_373_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = lean_box(0);
v___x_379_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__14));
v___x_380_ = l_Lean_Expr_const___override(v___x_379_, v___x_378_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15);
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = lean_box(0);
v___x_386_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__17));
v___x_387_ = l_Lean_Expr_const___override(v___x_386_, v___x_385_);
return v___x_387_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18);
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_box(0);
v___x_393_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__20));
v___x_394_ = l_Lean_Expr_const___override(v___x_393_, v___x_392_);
return v___x_394_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_box(0);
v___x_400_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__23));
v___x_401_ = l_Lean_Expr_const___override(v___x_400_, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_box(0);
v___x_407_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__26));
v___x_408_ = l_Lean_Expr_const___override(v___x_407_, v___x_406_);
return v___x_408_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27);
v___x_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5);
v___x_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8);
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(lean_object* v_x_417_){
_start:
{
if (lean_obj_tag(v_x_417_) == 1)
{
lean_object* v_pre_418_; 
v_pre_418_ = lean_ctor_get(v_x_417_, 0);
if (lean_obj_tag(v_pre_418_) == 0)
{
lean_object* v_str_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_str_419_ = lean_ctor_get(v_x_417_, 1);
v___x_420_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9));
v___x_421_ = lean_string_dec_eq(v_str_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6));
v___x_423_ = lean_string_dec_eq(v_str_419_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3));
v___x_425_ = lean_string_dec_eq(v_str_419_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__0));
v___x_427_ = lean_string_dec_eq(v_str_419_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__1));
v___x_429_ = lean_string_dec_eq(v_str_419_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__2));
v___x_431_ = lean_string_dec_eq(v_str_419_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__3));
v___x_433_ = lean_string_dec_eq(v_str_419_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__4));
v___x_435_ = lean_string_dec_eq(v_str_419_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__5));
v___x_437_ = lean_string_dec_eq(v_str_419_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__6));
v___x_439_ = lean_string_dec_eq(v_str_419_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
v___x_440_ = lean_box(0);
return v___x_440_;
}
else
{
lean_object* v___x_441_; 
v___x_441_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9);
return v___x_441_;
}
}
else
{
lean_object* v___x_442_; 
v___x_442_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13);
return v___x_442_;
}
}
else
{
lean_object* v___x_443_; 
v___x_443_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16);
return v___x_443_;
}
}
else
{
lean_object* v___x_444_; 
v___x_444_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19);
return v___x_444_;
}
}
else
{
lean_object* v___x_445_; 
v___x_445_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22);
return v___x_445_;
}
}
else
{
lean_object* v___x_446_; 
v___x_446_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25);
return v___x_446_;
}
}
else
{
lean_object* v___x_447_; 
v___x_447_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28);
return v___x_447_;
}
}
else
{
lean_object* v___x_448_; 
v___x_448_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29);
return v___x_448_;
}
}
else
{
lean_object* v___x_449_; 
v___x_449_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30);
return v___x_449_;
}
}
else
{
lean_object* v___x_450_; 
v___x_450_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31);
return v___x_450_;
}
}
else
{
lean_object* v___x_451_; 
v___x_451_ = lean_box(0);
return v___x_451_;
}
}
else
{
lean_object* v___x_452_; 
v___x_452_ = lean_box(0);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___boxed(lean_object* v_x_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(v_x_453_);
lean_dec(v_x_453_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(lean_object* v_msg_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___f_460_; lean_object* v___x_5554__overap_461_; lean_object* v___x_462_; 
v___f_460_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0));
v___x_5554__overap_461_ = lean_panic_fn_borrowed(v___f_460_, v_msg_456_);
lean_inc(v___y_458_);
lean_inc_ref(v___y_457_);
v___x_462_ = lean_apply_3(v___x_5554__overap_461_, v___y_457_, v___y_458_, lean_box(0));
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___boxed(lean_object* v_msg_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(v_msg_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0(lean_object* v_k_468_, lean_object* v_b_469_, lean_object* v_c_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v___x_476_; 
lean_inc(v___y_474_);
lean_inc_ref(v___y_473_);
lean_inc(v___y_472_);
lean_inc_ref(v___y_471_);
v___x_476_ = lean_apply_7(v_k_468_, v_b_469_, v_c_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, lean_box(0));
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0___boxed(lean_object* v_k_477_, lean_object* v_b_478_, lean_object* v_c_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0(v_k_477_, v_b_478_, v_c_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg(lean_object* v_type_486_, lean_object* v_k_487_, uint8_t v_cleanupAnnotations_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___f_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___f_494_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_494_, 0, v_k_487_);
v___x_495_ = 0;
v___x_496_ = lean_box(0);
v___x_497_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_495_, v___x_496_, v_type_486_, v___f_494_, v_cleanupAnnotations_488_, v___x_495_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
v_a_506_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_497_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_497_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___boxed(lean_object* v_type_514_, lean_object* v_k_515_, lean_object* v_cleanupAnnotations_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_522_; lean_object* v_res_523_; 
v_cleanupAnnotations_boxed_522_ = lean_unbox(v_cleanupAnnotations_516_);
v_res_523_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg(v_type_514_, v_k_515_, v_cleanupAnnotations_boxed_522_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2(lean_object* v_00_u03b1_524_, lean_object* v_type_525_, lean_object* v_k_526_, uint8_t v_cleanupAnnotations_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg(v_type_525_, v_k_526_, v_cleanupAnnotations_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___boxed(lean_object* v_00_u03b1_534_, lean_object* v_type_535_, lean_object* v_k_536_, lean_object* v_cleanupAnnotations_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_543_; lean_object* v_res_544_; 
v_cleanupAnnotations_boxed_543_ = lean_unbox(v_cleanupAnnotations_537_);
v_res_544_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2(v_00_u03b1_534_, v_type_535_, v_k_536_, v_cleanupAnnotations_boxed_543_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(lean_object* v_a_548_, lean_object* v_b_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_array_555_; lean_object* v_start_556_; lean_object* v_stop_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_614_; 
v_array_555_ = lean_ctor_get(v_a_548_, 0);
v_start_556_ = lean_ctor_get(v_a_548_, 1);
v_stop_557_ = lean_ctor_get(v_a_548_, 2);
v_isSharedCheck_614_ = !lean_is_exclusive(v_a_548_);
if (v_isSharedCheck_614_ == 0)
{
v___x_559_ = v_a_548_;
v_isShared_560_ = v_isSharedCheck_614_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_stop_557_);
lean_inc(v_start_556_);
lean_inc(v_array_555_);
lean_dec(v_a_548_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_614_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
uint8_t v___x_561_; 
v___x_561_ = lean_nat_dec_lt(v_start_556_, v_stop_557_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
lean_del_object(v___x_559_);
lean_dec(v_stop_557_);
lean_dec(v_start_556_);
lean_dec_ref(v_array_555_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v_b_549_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec_ref(v_b_549_);
v___x_563_ = lean_array_fget_borrowed(v_array_555_, v_start_556_);
v___x_564_ = l_Lean_Expr_fvarId_x21(v___x_563_);
v___x_565_ = l_Lean_FVarId_getType___redArg(v___x_564_, v___y_550_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_565_, 1);
v___x_567_ = l_Lean_Compiler_LCNF_toLCNFType(v_a_566_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_567_, 1);
v___x_569_ = l_Lean_Compiler_LCNF_toMonoType(v_a_568_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_589_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_589_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_589_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_589_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_box(0);
v___x_575_ = l_Lean_Expr_isErased(v_a_570_);
lean_dec(v_a_570_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
lean_del_object(v___x_559_);
lean_dec(v_stop_557_);
lean_dec(v_start_556_);
lean_dec_ref(v_array_555_);
v___x_576_ = lean_box(v___x_561_);
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_574_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_578_);
v___x_580_ = v___x_572_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
lean_del_object(v___x_572_);
v___x_582_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___closed__0));
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_nat_add(v_start_556_, v___x_583_);
lean_dec(v_start_556_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 1, v___x_584_);
v___x_586_ = v___x_559_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_array_555_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_stop_557_);
v___x_586_ = v_reuseFailAlloc_588_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v_a_548_ = v___x_586_;
v_b_549_ = v___x_582_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_del_object(v___x_559_);
lean_dec(v_stop_557_);
lean_dec(v_start_556_);
lean_dec_ref(v_array_555_);
v_a_590_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_569_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_569_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_del_object(v___x_559_);
lean_dec(v_stop_557_);
lean_dec(v_start_556_);
lean_dec_ref(v_array_555_);
v_a_598_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_567_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_567_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_del_object(v___x_559_);
lean_dec(v_stop_557_);
lean_dec(v_start_556_);
lean_dec_ref(v_array_555_);
v_a_606_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_565_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_565_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___boxed(lean_object* v_a_615_, lean_object* v_b_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(v_a_615_, v_b_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0(uint8_t v___x_623_, lean_object* v_numParams_624_, lean_object* v___x_625_, lean_object* v_params_626_, lean_object* v_x_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_lower_634_; lean_object* v_upper_635_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = lean_array_get_size(v_params_626_);
v___x_662_ = lean_nat_dec_le(v_numParams_624_, v___x_625_);
if (v___x_662_ == 0)
{
lean_dec(v___x_625_);
v_lower_634_ = v_numParams_624_;
v_upper_635_ = v___x_661_;
goto v___jp_633_;
}
else
{
lean_dec(v_numParams_624_);
v_lower_634_ = v___x_625_;
v_upper_635_ = v___x_661_;
goto v___jp_633_;
}
v___jp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = l_Array_toSubarray___redArg(v_params_626_, v_lower_634_, v_upper_635_);
v___x_637_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___closed__0));
v___x_638_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(v___x_636_, v___x_637_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_652_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_652_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_652_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_652_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_fst_643_; 
v_fst_643_ = lean_ctor_get(v_a_639_, 0);
lean_inc(v_fst_643_);
lean_dec(v_a_639_);
if (lean_obj_tag(v_fst_643_) == 0)
{
lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_644_ = lean_box(v___x_623_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_644_);
v___x_646_ = v___x_641_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
else
{
lean_object* v_val_648_; lean_object* v___x_650_; 
v_val_648_ = lean_ctor_get(v_fst_643_, 0);
lean_inc(v_val_648_);
lean_dec_ref_known(v_fst_643_, 1);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v_val_648_);
v___x_650_ = v___x_641_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_val_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
v_a_653_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_638_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_638_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0___boxed(lean_object* v___x_663_, lean_object* v_numParams_664_, lean_object* v___x_665_, lean_object* v_params_666_, lean_object* v_x_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
uint8_t v___x_6924__boxed_673_; lean_object* v_res_674_; 
v___x_6924__boxed_673_ = lean_unbox(v___x_663_);
v_res_674_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0(v___x_6924__boxed_673_, v_numParams_664_, v___x_665_, v_params_666_, v_x_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec_ref(v_x_667_);
return v_res_674_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_678_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_679_ = lean_unsigned_to_nat(58u);
v___x_680_ = lean_unsigned_to_nat(92u);
v___x_681_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__1));
v___x_682_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_683_ = l_mkPanicMessageWithDecl(v___x_682_, v___x_681_, v___x_680_, v___x_679_, v___x_678_);
return v___x_683_;
}
}
static uint64_t _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_690_; uint64_t v___x_691_; 
v___x_690_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__4));
v___x_691_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__6(void){
_start:
{
uint64_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = lean_uint64_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__5);
v___x_693_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__4));
v___x_694_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set_uint64(v___x_694_, sizeof(void*)*1, v___x_692_);
return v___x_694_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_695_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_unsigned_to_nat(32u);
v___x_699_ = lean_mk_empty_array_with_capacity(v___x_698_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10(void){
_start:
{
size_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_701_ = ((size_t)5ULL);
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_unsigned_to_nat(32u);
v___x_704_ = lean_mk_empty_array_with_capacity(v___x_703_);
v___x_705_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__9);
v___x_706_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___x_704_);
lean_ctor_set(v___x_706_, 2, v___x_702_);
lean_ctor_set(v___x_706_, 3, v___x_702_);
lean_ctor_set_usize(v___x_706_, 4, v___x_701_);
return v___x_706_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__11(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_707_ = lean_box(1);
v___x_708_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10);
v___x_709_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8);
v___x_710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v___x_708_);
lean_ctor_set(v___x_710_, 2, v___x_707_);
return v___x_710_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13(void){
_start:
{
uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_713_ = 1;
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = lean_box(0);
v___x_716_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__12));
v___x_717_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__11);
v___x_718_ = lean_box(1);
v___x_719_ = 0;
v___x_720_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__6);
v___x_721_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v___x_718_);
lean_ctor_set(v___x_721_, 2, v___x_717_);
lean_ctor_set(v___x_721_, 3, v___x_716_);
lean_ctor_set(v___x_721_, 4, v___x_715_);
lean_ctor_set(v___x_721_, 5, v___x_714_);
lean_ctor_set(v___x_721_, 6, v___x_715_);
lean_ctor_set_uint8(v___x_721_, sizeof(void*)*7, v___x_719_);
lean_ctor_set_uint8(v___x_721_, sizeof(void*)*7 + 1, v___x_719_);
lean_ctor_set_uint8(v___x_721_, sizeof(void*)*7 + 2, v___x_719_);
lean_ctor_set_uint8(v___x_721_, sizeof(void*)*7 + 3, v___x_713_);
return v___x_721_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__14(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8);
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
lean_ctor_set(v___x_724_, 2, v___x_723_);
lean_ctor_set(v___x_724_, 3, v___x_723_);
lean_ctor_set(v___x_724_, 4, v___x_722_);
lean_ctor_set(v___x_724_, 5, v___x_722_);
lean_ctor_set(v___x_724_, 6, v___x_722_);
lean_ctor_set(v___x_724_, 7, v___x_722_);
lean_ctor_set(v___x_724_, 8, v___x_722_);
lean_ctor_set(v___x_724_, 9, v___x_722_);
lean_ctor_set(v___x_724_, 10, v___x_722_);
return v___x_724_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__15(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8);
v___x_726_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
lean_ctor_set(v___x_726_, 2, v___x_725_);
lean_ctor_set(v___x_726_, 3, v___x_725_);
lean_ctor_set(v___x_726_, 4, v___x_725_);
lean_ctor_set(v___x_726_, 5, v___x_725_);
return v___x_726_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__16(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8);
v___x_728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
lean_ctor_set(v___x_728_, 2, v___x_727_);
lean_ctor_set(v___x_728_, 3, v___x_727_);
lean_ctor_set(v___x_728_, 4, v___x_727_);
return v___x_728_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_729_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__16, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__16_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__16);
v___x_730_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10);
v___x_731_ = lean_box(1);
v___x_732_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__15, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__15_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__15);
v___x_733_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__14);
v___x_734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v___x_732_);
lean_ctor_set(v___x_734_, 2, v___x_731_);
lean_ctor_set(v___x_734_, 3, v___x_730_);
lean_ctor_set(v___x_734_, 4, v___x_729_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(lean_object* v___x_735_, lean_object* v_as_x27_736_, lean_object* v_b_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
if (lean_obj_tag(v_as_x27_736_) == 0)
{
lean_object* v___x_741_; 
lean_dec_ref(v___x_735_);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v_b_737_);
return v___x_741_;
}
else
{
lean_object* v_head_742_; lean_object* v_tail_743_; uint8_t v_a_745_; lean_object* v___y_751_; lean_object* v___y_752_; uint8_t v___x_764_; lean_object* v___x_765_; 
v_head_742_ = lean_ctor_get(v_as_x27_736_, 0);
v_tail_743_ = lean_ctor_get(v_as_x27_736_, 1);
v___x_764_ = 0;
lean_inc(v_head_742_);
lean_inc_ref(v___x_735_);
v___x_765_ = l_Lean_Environment_find_x3f(v___x_735_, v_head_742_, v___x_764_);
if (lean_obj_tag(v___x_765_) == 1)
{
lean_object* v_val_766_; 
v_val_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_val_766_);
lean_dec_ref_known(v___x_765_, 1);
if (lean_obj_tag(v_val_766_) == 6)
{
lean_object* v_val_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v_toConstantVal_772_; lean_object* v_numParams_773_; lean_object* v_type_774_; lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___x_777_; 
v_val_767_ = lean_ctor_get(v_val_766_, 0);
lean_inc_ref(v_val_767_);
lean_dec_ref_known(v_val_766_, 1);
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13);
v___x_770_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17);
v___x_771_ = lean_st_mk_ref(v___x_770_);
v_toConstantVal_772_ = lean_ctor_get(v_val_767_, 0);
lean_inc_ref(v_toConstantVal_772_);
v_numParams_773_ = lean_ctor_get(v_val_767_, 3);
lean_inc(v_numParams_773_);
lean_dec_ref(v_val_767_);
v_type_774_ = lean_ctor_get(v_toConstantVal_772_, 2);
lean_inc_ref(v_type_774_);
lean_dec_ref(v_toConstantVal_772_);
v___x_775_ = lean_box(v___x_764_);
v___f_776_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_776_, 0, v___x_775_);
lean_closure_set(v___f_776_, 1, v_numParams_773_);
lean_closure_set(v___f_776_, 2, v___x_768_);
v___x_777_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg(v_type_774_, v___f_776_, v___x_764_, v___x_769_, v___x_771_, v___y_738_, v___y_739_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v___x_779_ = lean_st_ref_get(v___x_771_);
lean_dec(v___x_771_);
lean_dec(v___x_779_);
v___x_780_ = lean_unbox(v_a_778_);
lean_dec(v_a_778_);
v_a_745_ = v___x_780_;
goto v___jp_744_;
}
else
{
lean_dec(v___x_771_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_781_; uint8_t v___x_782_; 
v_a_781_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_777_, 1);
v___x_782_ = lean_unbox(v_a_781_);
lean_dec(v_a_781_);
v_a_745_ = v___x_782_;
goto v___jp_744_;
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_b_737_);
lean_dec_ref(v___x_735_);
v_a_783_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_777_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_777_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
else
{
lean_dec(v_val_766_);
v___y_751_ = v___y_738_;
v___y_752_ = v___y_739_;
goto v___jp_750_;
}
}
else
{
lean_dec(v___x_765_);
v___y_751_ = v___y_738_;
v___y_752_ = v___y_739_;
goto v___jp_750_;
}
v___jp_744_:
{
if (v_a_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_add(v_b_737_, v___x_746_);
lean_dec(v_b_737_);
v_as_x27_736_ = v_tail_743_;
v_b_737_ = v___x_747_;
goto _start;
}
else
{
v_as_x27_736_ = v_tail_743_;
goto _start;
}
}
v___jp_750_:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__3);
v___x_754_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(v___x_753_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_dec_ref_known(v___x_754_, 1);
v_as_x27_736_ = v_tail_743_;
goto _start;
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_b_737_);
lean_dec_ref(v___x_735_);
v_a_756_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_754_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_754_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___boxed(lean_object* v___x_791_, lean_object* v_as_x27_792_, lean_object* v_b_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(v___x_791_, v_as_x27_792_, v_b_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v_as_x27_792_);
return v_res_797_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_box(0);
v___x_802_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__1));
v___x_803_ = l_Lean_Expr_const___override(v___x_802_, v___x_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType(lean_object* v_name_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(v_name_804_);
if (lean_obj_tag(v___x_811_) == 1)
{
lean_object* v_val_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v_name_804_);
v_val_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_val_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 0);
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_val_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
else
{
lean_object* v___x_820_; lean_object* v_env_821_; uint8_t v___x_822_; lean_object* v___x_823_; 
lean_dec(v___x_811_);
v___x_820_ = lean_st_ref_get(v_a_806_);
v_env_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc_ref_n(v_env_821_, 2);
lean_dec(v___x_820_);
v___x_822_ = 0;
v___x_823_ = l_Lean_Environment_find_x3f(v_env_821_, v_name_804_, v___x_822_);
if (lean_obj_tag(v___x_823_) == 1)
{
lean_object* v_val_824_; 
v_val_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_val_824_);
lean_dec_ref_known(v___x_823_, 1);
if (lean_obj_tag(v_val_824_) == 5)
{
lean_object* v_val_825_; lean_object* v_ctors_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_val_825_ = lean_ctor_get(v_val_824_, 0);
lean_inc_ref(v_val_825_);
lean_dec_ref_known(v_val_824_, 1);
v_ctors_826_ = lean_ctor_get(v_val_825_, 4);
lean_inc(v_ctors_826_);
lean_dec_ref(v_val_825_);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(v_env_821_, v_ctors_826_, v___x_827_, v_a_805_, v_a_806_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_848_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_848_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_848_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_848_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = l_List_lengthTR___redArg(v_ctors_826_);
lean_dec(v_ctors_826_);
v___x_834_ = lean_nat_dec_eq(v_a_829_, v___x_833_);
if (v___x_834_ == 0)
{
uint8_t v___x_835_; 
lean_dec(v___x_833_);
v___x_835_ = lean_nat_dec_eq(v_a_829_, v___x_827_);
lean_dec(v_a_829_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_836_);
v___x_838_ = v___x_831_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_840_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_840_);
v___x_842_ = v___x_831_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_846_; 
lean_dec(v_a_829_);
v___x_844_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum(v___x_833_);
lean_dec(v___x_833_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_844_);
v___x_846_ = v___x_831_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec(v_ctors_826_);
v_a_849_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_828_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_828_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_dec(v_val_824_);
lean_dec_ref(v_env_821_);
goto v___jp_808_;
}
}
else
{
lean_dec(v___x_823_);
lean_dec_ref(v_env_821_);
goto v___jp_808_;
}
}
v___jp_808_:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___boxed(lean_object* v_name_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType(v_name_857_, v_a_858_, v_a_859_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1(lean_object* v_inst_862_, lean_object* v_R_863_, lean_object* v_a_864_, lean_object* v_b_865_, lean_object* v_c_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(v_a_864_, v_b_865_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___boxed(lean_object* v_inst_873_, lean_object* v_R_874_, lean_object* v_a_875_, lean_object* v_b_876_, lean_object* v_c_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1(v_inst_873_, v_R_874_, v_a_875_, v_b_876_, v_c_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3(lean_object* v___x_884_, lean_object* v_as_885_, lean_object* v_as_x27_886_, lean_object* v_b_887_, lean_object* v_a_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(v___x_884_, v_as_x27_886_, v_b_887_, v___y_889_, v___y_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___boxed(lean_object* v___x_893_, lean_object* v_as_894_, lean_object* v_as_x27_895_, lean_object* v_b_896_, lean_object* v_a_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3(v___x_893_, v_as_894_, v_as_x27_895_, v_b_896_, v_a_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v_as_x27_895_);
lean_dec(v_as_894_);
return v_res_901_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setImpureType___closed__0(void){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_902_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setImpureType___closed__1(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_obj_once(&l_Lean_Compiler_LCNF_setImpureType___closed__0, &l_Lean_Compiler_LCNF_setImpureType___closed__0_once, _init_l_Lean_Compiler_LCNF_setImpureType___closed__0);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setImpureType___closed__2(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_obj_once(&l_Lean_Compiler_LCNF_setImpureType___closed__1, &l_Lean_Compiler_LCNF_setImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_setImpureType___closed__1);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setImpureType(lean_object* v_name_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(v_name_907_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v___x_912_; lean_object* v_env_913_; lean_object* v___x_914_; lean_object* v_toEnvExtension_915_; lean_object* v_asyncMode_916_; lean_object* v___x_917_; uint8_t v___x_918_; lean_object* v___x_919_; 
v___x_912_ = lean_st_ref_get(v_a_909_);
v_env_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc_ref(v_env_913_);
lean_dec(v___x_912_);
v___x_914_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt;
v_toEnvExtension_915_ = lean_ctor_get(v___x_914_, 0);
v_asyncMode_916_ = lean_ctor_get(v_toEnvExtension_915_, 2);
v___x_917_ = l_Lean_instInhabitedExpr;
v___x_918_ = 0;
lean_inc(v_name_907_);
v___x_919_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_917_, v___x_914_, v_env_913_, v_name_907_, v_asyncMode_916_, v___x_918_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v___x_920_; 
lean_inc(v_name_907_);
v___x_920_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType(v_name_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_949_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_949_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_949_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_949_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v_env_926_; lean_object* v_nextMacroScope_927_; lean_object* v_ngen_928_; lean_object* v_auxDeclNGen_929_; lean_object* v_traceState_930_; lean_object* v_messages_931_; lean_object* v_infoState_932_; lean_object* v_snapshotTasks_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_947_; 
v___x_925_ = lean_st_ref_take(v_a_909_);
v_env_926_ = lean_ctor_get(v___x_925_, 0);
v_nextMacroScope_927_ = lean_ctor_get(v___x_925_, 1);
v_ngen_928_ = lean_ctor_get(v___x_925_, 2);
v_auxDeclNGen_929_ = lean_ctor_get(v___x_925_, 3);
v_traceState_930_ = lean_ctor_get(v___x_925_, 4);
v_messages_931_ = lean_ctor_get(v___x_925_, 6);
v_infoState_932_ = lean_ctor_get(v___x_925_, 7);
v_snapshotTasks_933_ = lean_ctor_get(v___x_925_, 8);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v___x_925_, 5);
lean_dec(v_unused_948_);
v___x_935_ = v___x_925_;
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_snapshotTasks_933_);
lean_inc(v_infoState_932_);
lean_inc(v_messages_931_);
lean_inc(v_traceState_930_);
lean_inc(v_auxDeclNGen_929_);
lean_inc(v_ngen_928_);
lean_inc(v_nextMacroScope_927_);
lean_inc(v_env_926_);
lean_dec(v___x_925_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_937_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_914_, v_env_926_, v_name_907_, v_a_921_);
v___x_938_ = lean_obj_once(&l_Lean_Compiler_LCNF_setImpureType___closed__2, &l_Lean_Compiler_LCNF_setImpureType___closed__2_once, _init_l_Lean_Compiler_LCNF_setImpureType___closed__2);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 5, v___x_938_);
lean_ctor_set(v___x_935_, 0, v___x_937_);
v___x_940_ = v___x_935_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_nextMacroScope_927_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_ngen_928_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_auxDeclNGen_929_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_traceState_930_);
lean_ctor_set(v_reuseFailAlloc_946_, 5, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_946_, 6, v_messages_931_);
lean_ctor_set(v_reuseFailAlloc_946_, 7, v_infoState_932_);
lean_ctor_set(v_reuseFailAlloc_946_, 8, v_snapshotTasks_933_);
v___x_940_ = v_reuseFailAlloc_946_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_941_ = lean_st_ref_put(v_a_909_, v___x_940_);
v___x_942_ = lean_box(0);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_942_);
v___x_944_ = v___x_923_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec(v_name_907_);
v_a_950_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_920_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_920_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_965_; 
lean_dec(v_name_907_);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v___x_919_, 0);
lean_dec(v_unused_966_);
v___x_959_ = v___x_919_;
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
else
{
lean_dec(v___x_919_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_box(0);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 0);
lean_ctor_set(v___x_959_, 0, v___x_961_);
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
else
{
lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_974_; 
lean_dec(v_name_907_);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; 
v_unused_975_ = lean_ctor_get(v___x_911_, 0);
lean_dec(v_unused_975_);
v___x_968_ = v___x_911_;
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
else
{
lean_dec(v___x_911_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_970_ = lean_box(0);
if (v_isShared_969_ == 0)
{
lean_ctor_set_tag(v___x_968_, 0);
lean_ctor_set(v___x_968_, 0, v___x_970_);
v___x_972_ = v___x_968_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setImpureType___boxed(lean_object* v_name_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Compiler_LCNF_setImpureType(v_name_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
return v_res_980_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_981_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_984_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1);
v___x_985_ = lean_unsigned_to_nat(0u);
v___x_986_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
lean_ctor_set(v___x_986_, 2, v___x_985_);
lean_ctor_set(v___x_986_, 3, v___x_985_);
lean_ctor_set(v___x_986_, 4, v___x_984_);
lean_ctor_set(v___x_986_, 5, v___x_984_);
lean_ctor_set(v___x_986_, 6, v___x_984_);
lean_ctor_set(v___x_986_, 7, v___x_984_);
lean_ctor_set(v___x_986_, 8, v___x_984_);
lean_ctor_set(v___x_986_, 9, v___x_984_);
lean_ctor_set(v___x_986_, 10, v___x_984_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_987_ = lean_box(1);
v___x_988_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10);
v___x_989_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1);
v___x_990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v___x_988_);
lean_ctor_set(v___x_990_, 2, v___x_987_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0(lean_object* v_msgData_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; lean_object* v_toCold_996_; lean_object* v_env_997_; lean_object* v_options_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_995_ = lean_st_ref_get(v___y_993_);
v_toCold_996_ = lean_ctor_get(v___y_992_, 0);
v_env_997_ = lean_ctor_get(v___x_995_, 0);
lean_inc_ref(v_env_997_);
lean_dec(v___x_995_);
v_options_998_ = lean_ctor_get(v_toCold_996_, 2);
v___x_999_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2);
v___x_1000_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3);
lean_inc_ref(v_options_998_);
v___x_1001_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1001_, 0, v_env_997_);
lean_ctor_set(v___x_1001_, 1, v___x_999_);
lean_ctor_set(v___x_1001_, 2, v___x_1000_);
lean_ctor_set(v___x_1001_, 3, v_options_998_);
v___x_1002_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v_msgData_991_);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___boxed(lean_object* v_msgData_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0(v_msgData_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(lean_object* v_msg_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_ref_1013_; lean_object* v___x_1014_; lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1023_; 
v_ref_1013_ = lean_ctor_get(v___y_1010_, 2);
v___x_1014_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0(v_msg_1009_, v___y_1010_, v___y_1011_);
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
lean_inc(v_ref_1013_);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v_ref_1013_);
lean_ctor_set(v___x_1019_, 1, v_a_1015_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set_tag(v___x_1017_, 1);
lean_ctor_set(v___x_1017_, 0, v___x_1019_);
v___x_1021_ = v___x_1017_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___boxed(lean_object* v_msg_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_msg_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1028_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l_Lean_Compiler_LCNF_nameToImpureType___closed__0));
v___x_1031_ = l_Lean_stringToMessageData(v___x_1030_);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__3(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l_Lean_Compiler_LCNF_nameToImpureType___closed__2));
v___x_1034_ = l_Lean_stringToMessageData(v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_nameToImpureType(lean_object* v_name_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(v_name_1035_);
if (lean_obj_tag(v___x_1042_) == 1)
{
lean_object* v_val_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec(v_name_1035_);
v_val_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_val_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 0);
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_val_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
else
{
lean_object* v___x_1051_; lean_object* v_env_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; 
lean_dec(v___x_1042_);
v___x_1051_ = lean_st_ref_get(v_a_1037_);
v_env_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc_ref(v_env_1052_);
lean_dec(v___x_1051_);
v___x_1053_ = 0;
lean_inc(v_name_1035_);
v___x_1054_ = l_Lean_Environment_find_x3f(v_env_1052_, v_name_1035_, v___x_1053_);
if (lean_obj_tag(v___x_1054_) == 1)
{
lean_object* v_val_1055_; 
v_val_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_val_1055_);
lean_dec_ref_known(v___x_1054_, 1);
if (lean_obj_tag(v_val_1055_) == 5)
{
lean_object* v___x_1056_; lean_object* v_env_1057_; lean_object* v___x_1058_; lean_object* v_toEnvExtension_1059_; lean_object* v_asyncMode_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; 
lean_dec_ref_known(v_val_1055_, 1);
v___x_1056_ = lean_st_ref_get(v_a_1037_);
v_env_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc_ref(v_env_1057_);
lean_dec(v___x_1056_);
v___x_1058_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt;
v_toEnvExtension_1059_ = lean_ctor_get(v___x_1058_, 0);
v_asyncMode_1060_ = lean_ctor_get(v_toEnvExtension_1059_, 2);
v___x_1061_ = l_Lean_instInhabitedExpr;
v___x_1062_ = 0;
lean_inc(v_name_1035_);
v___x_1063_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1061_, v___x_1058_, v_env_1057_, v_name_1035_, v_asyncMode_1060_, v___x_1062_);
if (lean_obj_tag(v___x_1063_) == 1)
{
lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v_name_1035_);
v_val_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_val_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec(v___x_1063_);
v___x_1072_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__1, &l_Lean_Compiler_LCNF_nameToImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1);
v___x_1073_ = l_Lean_MessageData_ofName(v_name_1035_);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__3, &l_Lean_Compiler_LCNF_nameToImpureType___closed__3_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__3);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v___x_1076_, v_a_1036_, v_a_1037_);
return v___x_1077_;
}
}
else
{
lean_dec(v_val_1055_);
lean_dec(v_name_1035_);
goto v___jp_1039_;
}
}
else
{
lean_dec(v___x_1054_);
lean_dec(v_name_1035_);
goto v___jp_1039_;
}
}
v___jp_1039_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_nameToImpureType___boxed(lean_object* v_name_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_Compiler_LCNF_nameToImpureType(v_name_1078_, v_a_1079_, v_a_1080_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0(lean_object* v_00_u03b1_1083_, lean_object* v_msg_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_msg_1084_, v___y_1085_, v___y_1086_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___boxed(lean_object* v_00_u03b1_1089_, lean_object* v_msg_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0(v_00_u03b1_1089_, v_msg_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
return v_res_1094_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(lean_object* v_type_1096_){
_start:
{
switch(lean_obj_tag(v_type_1096_))
{
case 4:
{
lean_object* v_declName_1097_; 
v_declName_1097_ = lean_ctor_get(v_type_1096_, 0);
if (lean_obj_tag(v_declName_1097_) == 1)
{
lean_object* v_pre_1098_; 
v_pre_1098_ = lean_ctor_get(v_declName_1097_, 0);
if (lean_obj_tag(v_pre_1098_) == 0)
{
lean_object* v_str_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_str_1099_ = lean_ctor_get(v_declName_1097_, 1);
v___x_1100_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___closed__0));
v___x_1101_ = lean_string_dec_eq(v_str_1099_, v___x_1100_);
return v___x_1101_;
}
else
{
uint8_t v___x_1102_; 
v___x_1102_ = 0;
return v___x_1102_;
}
}
else
{
uint8_t v___x_1103_; 
v___x_1103_ = 0;
return v___x_1103_;
}
}
case 7:
{
lean_object* v_body_1104_; 
v_body_1104_ = lean_ctor_get(v_type_1096_, 2);
v_type_1096_ = v_body_1104_;
goto _start;
}
default: 
{
uint8_t v___x_1106_; 
v___x_1106_ = 0;
return v___x_1106_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___boxed(lean_object* v_type_1107_){
_start:
{
uint8_t v_res_1108_; lean_object* v_r_1109_; 
v_res_1108_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(v_type_1107_);
lean_dec_ref(v_type_1107_);
v_r_1109_ = lean_box(v_res_1108_);
return v_r_1109_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(lean_object* v_msg_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___f_1114_; lean_object* v___x_877__overap_1115_; lean_object* v___x_1116_; 
v___f_1114_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0));
v___x_877__overap_1115_ = lean_panic_fn_borrowed(v___f_1114_, v_msg_1110_);
lean_inc(v___y_1112_);
lean_inc_ref(v___y_1111_);
v___x_1116_ = lean_apply_3(v___x_877__overap_1115_, v___y_1111_, v___y_1112_, lean_box(0));
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1___boxed(lean_object* v_msg_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(v_msg_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v_res_1121_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toImpureType___closed__1(void){
_start:
{
lean_object* v___x_1124_; lean_object* v_dummy_1125_; 
v___x_1124_ = lean_box(0);
v_dummy_1125_ = l_Lean_Expr_sort___override(v___x_1124_);
return v_dummy_1125_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toImpureType___closed__3(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1127_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_1128_ = lean_unsigned_to_nat(41u);
v___x_1129_ = lean_unsigned_to_nat(138u);
v___x_1130_ = ((lean_object*)(l_Lean_Compiler_LCNF_toImpureType___closed__2));
v___x_1131_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_1132_ = l_mkPanicMessageWithDecl(v___x_1131_, v___x_1130_, v___x_1129_, v___x_1128_, v___x_1127_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toImpureType___closed__4(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1133_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_1134_ = lean_unsigned_to_nat(9u);
v___x_1135_ = lean_unsigned_to_nat(150u);
v___x_1136_ = ((lean_object*)(l_Lean_Compiler_LCNF_toImpureType___closed__2));
v___x_1137_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_1138_ = l_mkPanicMessageWithDecl(v___x_1137_, v___x_1136_, v___x_1135_, v___x_1134_, v___x_1133_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpureType(lean_object* v_type_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
switch(lean_obj_tag(v_type_1139_))
{
case 4:
{
lean_object* v_declName_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_declName_1143_ = lean_ctor_get(v_type_1139_, 0);
lean_inc(v_declName_1143_);
lean_dec_ref_known(v_type_1139_, 2);
v___x_1144_ = ((lean_object*)(l_Lean_Compiler_LCNF_toImpureType___closed__0));
v___x_1145_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(v_declName_1143_, v___x_1144_, v_a_1140_, v_a_1141_);
return v___x_1145_;
}
case 5:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Expr_getAppFn(v_type_1139_);
if (lean_obj_tag(v___x_1146_) == 4)
{
lean_object* v_declName_1147_; lean_object* v_dummy_1148_; lean_object* v_nargs_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_declName_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_declName_1147_);
lean_dec_ref_known(v___x_1146_, 2);
v_dummy_1148_ = lean_obj_once(&l_Lean_Compiler_LCNF_toImpureType___closed__1, &l_Lean_Compiler_LCNF_toImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_toImpureType___closed__1);
v_nargs_1149_ = l_Lean_Expr_getAppNumArgs(v_type_1139_);
lean_inc(v_nargs_1149_);
v___x_1150_ = lean_mk_array(v_nargs_1149_, v_dummy_1148_);
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_nat_sub(v_nargs_1149_, v___x_1151_);
lean_dec(v_nargs_1149_);
v___x_1153_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_type_1139_, v___x_1150_, v___x_1152_);
v___x_1154_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(v_declName_1147_, v___x_1153_, v_a_1140_, v_a_1141_);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec_ref_known(v_type_1139_, 2);
lean_dec_ref(v___x_1146_);
v___x_1155_ = lean_obj_once(&l_Lean_Compiler_LCNF_toImpureType___closed__3, &l_Lean_Compiler_LCNF_toImpureType___closed__3_once, _init_l_Lean_Compiler_LCNF_toImpureType___closed__3);
v___x_1156_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(v___x_1155_, v_a_1140_, v_a_1141_);
return v___x_1156_;
}
}
case 7:
{
lean_object* v_body_1157_; uint8_t v___x_1158_; 
v_body_1157_ = lean_ctor_get(v_type_1139_, 2);
lean_inc_ref(v_body_1157_);
lean_dec_ref_known(v_type_1139_, 3);
v___x_1158_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(v_body_1157_);
lean_dec_ref(v_body_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
case 10:
{
lean_object* v_expr_1163_; 
v_expr_1163_ = lean_ctor_get(v_type_1139_, 1);
lean_inc_ref(v_expr_1163_);
lean_dec_ref_known(v_type_1139_, 2);
v_type_1139_ = v_expr_1163_;
goto _start;
}
default: 
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec_ref(v_type_1139_);
v___x_1165_ = lean_obj_once(&l_Lean_Compiler_LCNF_toImpureType___closed__4, &l_Lean_Compiler_LCNF_toImpureType___closed__4_once, _init_l_Lean_Compiler_LCNF_toImpureType___closed__4);
v___x_1166_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(v___x_1165_, v_a_1140_, v_a_1141_);
return v___x_1166_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(lean_object* v_declName_1167_, lean_object* v_args_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v___x_1172_; 
lean_inc(v_declName_1167_);
v___x_1172_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_declName_1167_, v_a_1169_, v_a_1170_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
if (lean_obj_tag(v_a_1173_) == 1)
{
lean_object* v_val_1174_; lean_object* v_ctorName_1175_; lean_object* v_numParams_1176_; lean_object* v_fieldIdx_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec(v_declName_1167_);
v_val_1174_ = lean_ctor_get(v_a_1173_, 0);
lean_inc(v_val_1174_);
lean_dec_ref_known(v_a_1173_, 1);
v_ctorName_1175_ = lean_ctor_get(v_val_1174_, 0);
lean_inc(v_ctorName_1175_);
v_numParams_1176_ = lean_ctor_get(v_val_1174_, 1);
lean_inc(v_numParams_1176_);
v_fieldIdx_1177_ = lean_ctor_get(v_val_1174_, 2);
lean_inc(v_fieldIdx_1177_);
lean_dec(v_val_1174_);
v___x_1178_ = lean_box(0);
v___x_1179_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_ctorName_1175_, v___x_1178_, v_a_1169_, v_a_1170_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref_known(v___x_1179_, 1);
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = l_Array_toSubarray___redArg(v_args_1168_, v___x_1181_, v_numParams_1176_);
v___x_1183_ = l_Subarray_copy___redArg(v___x_1182_);
v___x_1184_ = l_Lean_Compiler_LCNF_instantiateForall(v_a_1180_, v___x_1183_, v_a_1169_, v_a_1170_);
lean_dec_ref(v___x_1183_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1184_, 1);
v___x_1186_ = l_Lean_instInhabitedExpr;
v___x_1187_ = l_Lean_Compiler_LCNF_getParamTypes(v_a_1185_);
v___x_1188_ = lean_array_get(v___x_1186_, v___x_1187_, v_fieldIdx_1177_);
lean_dec(v_fieldIdx_1177_);
lean_dec_ref(v___x_1187_);
v___x_1189_ = l_Lean_Compiler_LCNF_toMonoType(v___x_1188_, v_a_1169_, v_a_1170_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1191_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1189_, 1);
v___x_1191_ = l_Lean_Compiler_LCNF_toImpureType(v_a_1190_, v_a_1169_, v_a_1170_);
return v___x_1191_;
}
else
{
return v___x_1189_;
}
}
else
{
lean_dec(v_fieldIdx_1177_);
return v___x_1184_;
}
}
else
{
lean_dec(v_fieldIdx_1177_);
lean_dec(v_numParams_1176_);
lean_dec_ref(v_args_1168_);
return v___x_1179_;
}
}
else
{
lean_object* v___x_1192_; 
lean_dec(v_a_1173_);
lean_dec_ref(v_args_1168_);
v___x_1192_ = l_Lean_Compiler_LCNF_nameToImpureType(v_declName_1167_, v_a_1169_, v_a_1170_);
return v___x_1192_;
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref(v_args_1168_);
lean_dec(v_declName_1167_);
v_a_1193_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1172_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1172_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp___boxed(lean_object* v_declName_1201_, lean_object* v_args_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(v_declName_1201_, v_args_1202_, v_a_1203_, v_a_1204_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpureType___boxed(lean_object* v_type_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1207_, v_a_1208_, v_a_1209_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx(lean_object* v_x_1212_){
_start:
{
switch(lean_obj_tag(v_x_1212_))
{
case 0:
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_unsigned_to_nat(0u);
return v___x_1213_;
}
case 1:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_unsigned_to_nat(1u);
return v___x_1214_;
}
case 2:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_unsigned_to_nat(2u);
return v___x_1215_;
}
case 3:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_unsigned_to_nat(3u);
return v___x_1216_;
}
default: 
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_unsigned_to_nat(4u);
return v___x_1217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx___boxed(lean_object* v_x_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx(v_x_1218_);
lean_dec(v_x_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(lean_object* v_t_1220_, lean_object* v_k_1221_){
_start:
{
switch(lean_obj_tag(v_t_1220_))
{
case 1:
{
lean_object* v_i_1222_; lean_object* v_type_1223_; lean_object* v___x_1224_; 
v_i_1222_ = lean_ctor_get(v_t_1220_, 0);
lean_inc(v_i_1222_);
v_type_1223_ = lean_ctor_get(v_t_1220_, 1);
lean_inc_ref(v_type_1223_);
lean_dec_ref_known(v_t_1220_, 2);
v___x_1224_ = lean_apply_2(v_k_1221_, v_i_1222_, v_type_1223_);
return v___x_1224_;
}
case 2:
{
lean_object* v_i_1225_; lean_object* v___x_1226_; 
v_i_1225_ = lean_ctor_get(v_t_1220_, 0);
lean_inc(v_i_1225_);
lean_dec_ref_known(v_t_1220_, 1);
v___x_1226_ = lean_apply_1(v_k_1221_, v_i_1225_);
return v___x_1226_;
}
case 3:
{
lean_object* v_sz_1227_; lean_object* v_offset_1228_; lean_object* v_type_1229_; lean_object* v___x_1230_; 
v_sz_1227_ = lean_ctor_get(v_t_1220_, 0);
lean_inc(v_sz_1227_);
v_offset_1228_ = lean_ctor_get(v_t_1220_, 1);
lean_inc(v_offset_1228_);
v_type_1229_ = lean_ctor_get(v_t_1220_, 2);
lean_inc_ref(v_type_1229_);
lean_dec_ref_known(v_t_1220_, 3);
v___x_1230_ = lean_apply_3(v_k_1221_, v_sz_1227_, v_offset_1228_, v_type_1229_);
return v___x_1230_;
}
default: 
{
lean_dec(v_t_1220_);
return v_k_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim(lean_object* v_motive_1231_, lean_object* v_ctorIdx_1232_, lean_object* v_t_1233_, lean_object* v_h_1234_, lean_object* v_k_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1233_, v_k_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___boxed(lean_object* v_motive_1237_, lean_object* v_ctorIdx_1238_, lean_object* v_t_1239_, lean_object* v_h_1240_, lean_object* v_k_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim(v_motive_1237_, v_ctorIdx_1238_, v_t_1239_, v_h_1240_, v_k_1241_);
lean_dec(v_ctorIdx_1238_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_erased_elim___redArg(lean_object* v_t_1243_, lean_object* v_erased_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1243_, v_erased_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_erased_elim(lean_object* v_motive_1246_, lean_object* v_t_1247_, lean_object* v_h_1248_, lean_object* v_erased_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1247_, v_erased_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_object_elim___redArg(lean_object* v_t_1251_, lean_object* v_object_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1251_, v_object_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_object_elim(lean_object* v_motive_1254_, lean_object* v_t_1255_, lean_object* v_h_1256_, lean_object* v_object_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1255_, v_object_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_usize_elim___redArg(lean_object* v_t_1259_, lean_object* v_usize_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1259_, v_usize_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_usize_elim(lean_object* v_motive_1262_, lean_object* v_t_1263_, lean_object* v_h_1264_, lean_object* v_usize_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1263_, v_usize_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_scalar_elim___redArg(lean_object* v_t_1267_, lean_object* v_scalar_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1267_, v_scalar_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_scalar_elim(lean_object* v_motive_1270_, lean_object* v_t_1271_, lean_object* v_h_1272_, lean_object* v_scalar_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1271_, v_scalar_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_void_elim___redArg(lean_object* v_t_1275_, lean_object* v_void_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1275_, v_void_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_void_elim(lean_object* v_motive_1278_, lean_object* v_t_1279_, lean_object* v_h_1280_, lean_object* v_void_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1279_, v_void_1281_);
return v___x_1282_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo_default(void){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_box(0);
return v___x_1283_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo(void){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_box(0);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format(lean_object* v_x_1306_){
_start:
{
switch(lean_obj_tag(v_x_1306_))
{
case 0:
{
lean_object* v___x_1307_; 
v___x_1307_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__1));
return v___x_1307_;
}
case 1:
{
lean_object* v_i_1308_; lean_object* v_type_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1324_; 
v_i_1308_ = lean_ctor_get(v_x_1306_, 0);
v_type_1309_ = lean_ctor_get(v_x_1306_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_x_1306_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1311_ = v_x_1306_;
v_isShared_1312_ = v_isSharedCheck_1324_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_type_1309_);
lean_inc(v_i_1308_);
lean_dec(v_x_1306_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1324_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1313_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__3));
v___x_1314_ = l_Nat_reprFast(v_i_1308_);
v___x_1315_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set_tag(v___x_1311_, 5);
lean_ctor_set(v___x_1311_, 1, v___x_1315_);
lean_ctor_set(v___x_1311_, 0, v___x_1313_);
v___x_1317_ = v___x_1311_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1318_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5));
v___x_1319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1317_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = lean_expr_dbg_to_string(v_type_1309_);
lean_dec_ref(v_type_1309_);
v___x_1321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
v___x_1322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1319_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
return v___x_1322_;
}
}
}
case 2:
{
lean_object* v_i_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1335_; 
v_i_1325_ = lean_ctor_get(v_x_1306_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_x_1306_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1327_ = v_x_1306_;
v_isShared_1328_ = v_isSharedCheck_1335_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_i_1325_);
lean_dec(v_x_1306_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1335_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1329_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__7));
v___x_1330_ = l_Nat_reprFast(v_i_1325_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 3);
lean_ctor_set(v___x_1327_, 0, v___x_1330_);
v___x_1332_ = v___x_1327_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1329_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
return v___x_1333_;
}
}
}
case 3:
{
lean_object* v_sz_1336_; lean_object* v_offset_1337_; lean_object* v_type_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_sz_1336_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_sz_1336_);
v_offset_1337_ = lean_ctor_get(v_x_1306_, 1);
lean_inc(v_offset_1337_);
v_type_1338_ = lean_ctor_get(v_x_1306_, 2);
lean_inc_ref(v_type_1338_);
lean_dec_ref_known(v_x_1306_, 3);
v___x_1339_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__9));
v___x_1340_ = l_Nat_reprFast(v_sz_1336_);
v___x_1341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
v___x_1342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1339_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__11));
v___x_1344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = l_Nat_reprFast(v_offset_1337_);
v___x_1346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
v___x_1347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1344_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5));
v___x_1349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1347_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
v___x_1350_ = lean_expr_dbg_to_string(v_type_1338_);
lean_dec_ref(v_type_1338_);
v___x_1351_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
v___x_1352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1349_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
return v___x_1352_;
}
default: 
{
lean_object* v___x_1353_; 
v___x_1353_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__13));
return v___x_1353_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1358_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0));
v___x_1359_ = l_Lean_Compiler_LCNF_instInhabitedCtorInfo_default;
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v___x_1358_);
return v___x_1360_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default(void){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1);
return v___x_1361_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout(void){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(lean_object* v_env_1363_, lean_object* v_as_1364_, size_t v_i_1365_, size_t v_stop_1366_, lean_object* v_b_1367_){
_start:
{
lean_object* v___y_1369_; uint8_t v___x_1373_; 
v___x_1373_ = lean_usize_dec_eq(v_i_1365_, v_stop_1366_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v_fst_1375_; uint8_t v___x_1376_; 
v___x_1374_ = lean_array_uget_borrowed(v_as_1364_, v_i_1365_);
v_fst_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_fst_1375_);
lean_inc_ref(v_env_1363_);
v___x_1376_ = l_Lean_Environment_contains(v_env_1363_, v_fst_1375_, v___x_1373_);
if (v___x_1376_ == 0)
{
v___y_1369_ = v_b_1367_;
goto v___jp_1368_;
}
else
{
lean_object* v___x_1377_; 
lean_inc(v___x_1374_);
v___x_1377_ = lean_array_push(v_b_1367_, v___x_1374_);
v___y_1369_ = v___x_1377_;
goto v___jp_1368_;
}
}
else
{
lean_dec_ref(v_env_1363_);
return v_b_1367_;
}
v___jp_1368_:
{
size_t v___x_1370_; size_t v___x_1371_; 
v___x_1370_ = ((size_t)1ULL);
v___x_1371_ = lean_usize_add(v_i_1365_, v___x_1370_);
v_i_1365_ = v___x_1371_;
v_b_1367_ = v___y_1369_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_1378_, lean_object* v_as_1379_, lean_object* v_i_1380_, lean_object* v_stop_1381_, lean_object* v_b_1382_){
_start:
{
size_t v_i_boxed_1383_; size_t v_stop_boxed_1384_; lean_object* v_res_1385_; 
v_i_boxed_1383_ = lean_unbox_usize(v_i_1380_);
lean_dec(v_i_1380_);
v_stop_boxed_1384_ = lean_unbox_usize(v_stop_1381_);
lean_dec(v_stop_1381_);
v_res_1385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(v_env_1378_, v_as_1379_, v_i_boxed_1383_, v_stop_boxed_1384_, v_b_1382_);
lean_dec_ref(v_as_1379_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_1386_, lean_object* v_x_1387_){
_start:
{
if (lean_obj_tag(v_x_1387_) == 0)
{
lean_object* v_k_1388_; lean_object* v_v_1389_; lean_object* v_l_1390_; lean_object* v_r_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v_k_1388_ = lean_ctor_get(v_x_1387_, 1);
v_v_1389_ = lean_ctor_get(v_x_1387_, 2);
v_l_1390_ = lean_ctor_get(v_x_1387_, 3);
v_r_1391_ = lean_ctor_get(v_x_1387_, 4);
v___x_1392_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0_spec__0(v_init_1386_, v_l_1390_);
lean_inc(v_v_1389_);
lean_inc(v_k_1388_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v_k_1388_);
lean_ctor_set(v___x_1393_, 1, v_v_1389_);
v___x_1394_ = lean_array_push(v___x_1392_, v___x_1393_);
v_init_1386_ = v___x_1394_;
v_x_1387_ = v_r_1391_;
goto _start;
}
else
{
return v_init_1386_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_1396_, lean_object* v_x_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0_spec__0(v_init_1396_, v_x_1397_);
lean_dec(v_x_1397_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(lean_object* v___x_1399_, lean_object* v_env_1400_, lean_object* v_s_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1402_ = lean_mk_empty_array_with_capacity(v___x_1399_);
v___x_1403_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0_spec__0(v___x_1402_, v_s_1401_);
v___x_1404_ = lean_array_get_size(v___x_1403_);
v___x_1405_ = lean_mk_empty_array_with_capacity(v___x_1399_);
v___x_1406_ = lean_nat_dec_lt(v___x_1399_, v___x_1404_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
lean_dec_ref(v___x_1403_);
lean_dec_ref(v_env_1400_);
lean_inc_ref_n(v___x_1405_, 2);
v___x_1407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1405_);
lean_ctor_set(v___x_1407_, 1, v___x_1405_);
lean_ctor_set(v___x_1407_, 2, v___x_1405_);
return v___x_1407_;
}
else
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_nat_dec_le(v___x_1404_, v___x_1404_);
if (v___x_1408_ == 0)
{
if (v___x_1406_ == 0)
{
lean_object* v___x_1409_; 
lean_dec_ref(v___x_1403_);
lean_dec_ref(v_env_1400_);
lean_inc_ref_n(v___x_1405_, 2);
v___x_1409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1405_);
lean_ctor_set(v___x_1409_, 1, v___x_1405_);
lean_ctor_set(v___x_1409_, 2, v___x_1405_);
return v___x_1409_;
}
else
{
size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1410_ = ((size_t)0ULL);
v___x_1411_ = lean_usize_of_nat(v___x_1404_);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(v_env_1400_, v___x_1403_, v___x_1410_, v___x_1411_, v___x_1405_);
lean_dec_ref(v___x_1403_);
lean_inc_ref_n(v___x_1412_, 2);
v___x_1413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
lean_ctor_set(v___x_1413_, 2, v___x_1412_);
return v___x_1413_;
}
}
else
{
size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = lean_usize_of_nat(v___x_1404_);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(v_env_1400_, v___x_1403_, v___x_1414_, v___x_1415_, v___x_1405_);
lean_dec_ref(v___x_1403_);
lean_inc_ref_n(v___x_1416_, 2);
v___x_1417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
lean_ctor_set(v___x_1417_, 2, v___x_1416_);
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2____boxed(lean_object* v___x_1418_, lean_object* v_env_1419_, lean_object* v_s_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(v___x_1418_, v_env_1419_, v_s_1420_);
lean_dec(v_s_1420_);
lean_dec(v___x_1418_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___f_1429_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_));
v___x_1430_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_));
v___x_1431_ = lean_box(0);
v___x_1432_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_1430_, v___x_1431_, v___f_1429_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2____boxed(lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_();
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(lean_object* v_init_1435_, lean_object* v_t_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0_spec__0(v_init_1435_, v_t_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_1438_, lean_object* v_t_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(v_init_1438_, v_t_1439_);
lean_dec(v_t_1439_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout(lean_object* v_layout_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v_ctorInfo_1445_; lean_object* v___x_1446_; 
v_ctorInfo_1445_ = lean_ctor_get(v_layout_1441_, 0);
lean_inc_ref(v_ctorInfo_1445_);
lean_dec_ref(v_layout_1441_);
v___x_1446_ = l_Lean_Compiler_LCNF_CtorInfo_checkValid(v_ctorInfo_1445_, v_a_1442_, v_a_1443_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout___boxed(lean_object* v_layout_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout(v_layout_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(lean_object* v_msg_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___f_1456_; lean_object* v___x_11579__overap_1457_; lean_object* v___x_1458_; 
v___f_1456_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0));
v___x_11579__overap_1457_ = lean_panic_fn_borrowed(v___f_1456_, v_msg_1452_);
lean_inc(v___y_1454_);
lean_inc_ref(v___y_1453_);
v___x_1458_ = lean_apply_3(v___x_11579__overap_1457_, v___y_1453_, v___y_1454_, lean_box(0));
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1___boxed(lean_object* v_msg_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(v_msg_1459_, v___y_1460_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(lean_object* v_msg_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___f_1471_; lean_object* v___x_11589__overap_1472_; lean_object* v___x_1473_; 
v___f_1471_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___closed__0));
v___x_11589__overap_1472_ = lean_panic_fn_borrowed(v___f_1471_, v_msg_1465_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
v___x_1473_ = lean_apply_5(v___x_11589__overap_1472_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, lean_box(0));
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___boxed(lean_object* v_msg_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(v_msg_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg(lean_object* v_type_1481_, lean_object* v_k_1482_, uint8_t v_cleanupAnnotations_1483_, uint8_t v_whnfType_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___f_1490_; lean_object* v___x_1491_; 
v___f_1490_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1490_, 0, v_k_1482_);
v___x_1491_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1481_, v___f_1490_, v_cleanupAnnotations_1483_, v_whnfType_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
v_a_1500_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1491_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1491_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg___boxed(lean_object* v_type_1508_, lean_object* v_k_1509_, lean_object* v_cleanupAnnotations_1510_, lean_object* v_whnfType_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1517_; uint8_t v_whnfType_boxed_1518_; lean_object* v_res_1519_; 
v_cleanupAnnotations_boxed_1517_ = lean_unbox(v_cleanupAnnotations_1510_);
v_whnfType_boxed_1518_ = lean_unbox(v_whnfType_1511_);
v_res_1519_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg(v_type_1508_, v_k_1509_, v_cleanupAnnotations_boxed_1517_, v_whnfType_boxed_1518_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5(lean_object* v_00_u03b1_1520_, lean_object* v_type_1521_, lean_object* v_k_1522_, uint8_t v_cleanupAnnotations_1523_, uint8_t v_whnfType_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg(v_type_1521_, v_k_1522_, v_cleanupAnnotations_1523_, v_whnfType_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___boxed(lean_object* v_00_u03b1_1531_, lean_object* v_type_1532_, lean_object* v_k_1533_, lean_object* v_cleanupAnnotations_1534_, lean_object* v_whnfType_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1541_; uint8_t v_whnfType_boxed_1542_; lean_object* v_res_1543_; 
v_cleanupAnnotations_boxed_1541_ = lean_unbox(v_cleanupAnnotations_1534_);
v_whnfType_boxed_1542_ = lean_unbox(v_whnfType_1535_);
v_res_1543_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5(v_00_u03b1_1531_, v_type_1532_, v_k_1533_, v_cleanupAnnotations_boxed_1541_, v_whnfType_boxed_1542_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(lean_object* v_size_1544_, size_t v_sz_1545_, size_t v_i_1546_, lean_object* v_bs_1547_, lean_object* v___y_1548_){
_start:
{
uint8_t v___x_1549_; 
v___x_1549_ = lean_usize_dec_lt(v_i_1546_, v_sz_1545_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v_bs_1547_);
lean_ctor_set(v___x_1550_, 1, v___y_1548_);
return v___x_1550_;
}
else
{
lean_object* v_v_1551_; lean_object* v___x_1552_; lean_object* v_bs_x27_1553_; lean_object* v_fst_1555_; lean_object* v_snd_1556_; 
v_v_1551_ = lean_array_uget(v_bs_1547_, v_i_1546_);
v___x_1552_ = lean_unsigned_to_nat(0u);
v_bs_x27_1553_ = lean_array_uset(v_bs_1547_, v_i_1546_, v___x_1552_);
switch(lean_obj_tag(v_v_1551_))
{
case 1:
{
v_fst_1555_ = v_v_1551_;
v_snd_1556_ = v___y_1548_;
goto v___jp_1554_;
}
case 2:
{
v_fst_1555_ = v_v_1551_;
v_snd_1556_ = v___y_1548_;
goto v___jp_1554_;
}
case 3:
{
lean_object* v_sz_1561_; lean_object* v_type_1562_; uint8_t v___x_1563_; 
v_sz_1561_ = lean_ctor_get(v_v_1551_, 0);
v_type_1562_ = lean_ctor_get(v_v_1551_, 2);
v___x_1563_ = lean_nat_dec_eq(v_sz_1561_, v_size_1544_);
if (v___x_1563_ == 0)
{
v_fst_1555_ = v_v_1551_;
v_snd_1556_ = v___y_1548_;
goto v___jp_1554_;
}
else
{
lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1571_; 
lean_inc_ref(v_type_1562_);
lean_inc(v_sz_1561_);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_v_1551_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; lean_object* v_unused_1573_; lean_object* v_unused_1574_; 
v_unused_1572_ = lean_ctor_get(v_v_1551_, 2);
lean_dec(v_unused_1572_);
v_unused_1573_ = lean_ctor_get(v_v_1551_, 1);
lean_dec(v_unused_1573_);
v_unused_1574_ = lean_ctor_get(v_v_1551_, 0);
lean_dec(v_unused_1574_);
v___x_1565_ = v_v_1551_;
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
else
{
lean_dec(v_v_1551_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1567_ = lean_nat_add(v___y_1548_, v_sz_1561_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 1, v___y_1548_);
v___x_1569_ = v___x_1565_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_sz_1561_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v___y_1548_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_type_1562_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
v_fst_1555_ = v___x_1569_;
v_snd_1556_ = v___x_1567_;
goto v___jp_1554_;
}
}
}
}
default: 
{
v_fst_1555_ = v_v_1551_;
v_snd_1556_ = v___y_1548_;
goto v___jp_1554_;
}
}
v___jp_1554_:
{
size_t v___x_1557_; size_t v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = ((size_t)1ULL);
v___x_1558_ = lean_usize_add(v_i_1546_, v___x_1557_);
v___x_1559_ = lean_array_uset(v_bs_x27_1553_, v_i_1546_, v_fst_1555_);
v_i_1546_ = v___x_1558_;
v_bs_1547_ = v___x_1559_;
v___y_1548_ = v_snd_1556_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0___boxed(lean_object* v_size_1575_, lean_object* v_sz_1576_, lean_object* v_i_1577_, lean_object* v_bs_1578_, lean_object* v___y_1579_){
_start:
{
size_t v_sz_boxed_1580_; size_t v_i_boxed_1581_; lean_object* v_res_1582_; 
v_sz_boxed_1580_ = lean_unbox_usize(v_sz_1576_);
lean_dec(v_sz_1576_);
v_i_boxed_1581_ = lean_unbox_usize(v_i_1577_);
lean_dec(v_i_1577_);
v_res_1582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(v_size_1575_, v_sz_boxed_1580_, v_i_boxed_1581_, v_bs_1578_, v___y_1579_);
lean_dec(v_size_1575_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0(lean_object* v_fields_1583_, lean_object* v_size_1584_, lean_object* v_nextOffset_1585_){
_start:
{
size_t v_sz_1586_; size_t v___x_1587_; lean_object* v___x_1588_; 
v_sz_1586_ = lean_array_size(v_fields_1583_);
v___x_1587_ = ((size_t)0ULL);
v___x_1588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(v_size_1584_, v_sz_1586_, v___x_1587_, v_fields_1583_, v_nextOffset_1585_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0___boxed(lean_object* v_fields_1589_, lean_object* v_size_1590_, lean_object* v_nextOffset_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0(v_fields_1589_, v_size_1590_, v_nextOffset_1591_);
lean_dec(v_size_1590_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(size_t v_sz_1593_, size_t v_i_1594_, lean_object* v_bs_1595_, lean_object* v___y_1596_){
_start:
{
uint8_t v___x_1597_; 
v___x_1597_ = lean_usize_dec_lt(v_i_1594_, v_sz_1593_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_bs_1595_);
lean_ctor_set(v___x_1598_, 1, v___y_1596_);
return v___x_1598_;
}
else
{
lean_object* v_v_1599_; lean_object* v___x_1600_; lean_object* v_bs_x27_1601_; lean_object* v_fst_1603_; lean_object* v_snd_1604_; 
v_v_1599_ = lean_array_uget(v_bs_1595_, v_i_1594_);
v___x_1600_ = lean_unsigned_to_nat(0u);
v_bs_x27_1601_ = lean_array_uset(v_bs_1595_, v_i_1594_, v___x_1600_);
switch(lean_obj_tag(v_v_1599_))
{
case 1:
{
v_fst_1603_ = v_v_1599_;
v_snd_1604_ = v___y_1596_;
goto v___jp_1602_;
}
case 2:
{
lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1617_; 
v_isSharedCheck_1617_ = !lean_is_exclusive(v_v_1599_);
if (v_isSharedCheck_1617_ == 0)
{
lean_object* v_unused_1618_; 
v_unused_1618_ = lean_ctor_get(v_v_1599_, 0);
lean_dec(v_unused_1618_);
v___x_1610_ = v_v_1599_;
v_isShared_1611_ = v_isSharedCheck_1617_;
goto v_resetjp_1609_;
}
else
{
lean_dec(v_v_1599_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1617_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1612_ = lean_unsigned_to_nat(1u);
v___x_1613_ = lean_nat_add(v___y_1596_, v___x_1612_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___y_1596_);
v___x_1615_ = v___x_1610_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___y_1596_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
v_fst_1603_ = v___x_1615_;
v_snd_1604_ = v___x_1613_;
goto v___jp_1602_;
}
}
}
case 3:
{
v_fst_1603_ = v_v_1599_;
v_snd_1604_ = v___y_1596_;
goto v___jp_1602_;
}
default: 
{
v_fst_1603_ = v_v_1599_;
v_snd_1604_ = v___y_1596_;
goto v___jp_1602_;
}
}
v___jp_1602_:
{
size_t v___x_1605_; size_t v___x_1606_; lean_object* v___x_1607_; 
v___x_1605_ = ((size_t)1ULL);
v___x_1606_ = lean_usize_add(v_i_1594_, v___x_1605_);
v___x_1607_ = lean_array_uset(v_bs_x27_1601_, v_i_1594_, v_fst_1603_);
v_i_1594_ = v___x_1606_;
v_bs_1595_ = v___x_1607_;
v___y_1596_ = v_snd_1604_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4___boxed(lean_object* v_sz_1619_, lean_object* v_i_1620_, lean_object* v_bs_1621_, lean_object* v___y_1622_){
_start:
{
size_t v_sz_boxed_1623_; size_t v_i_boxed_1624_; lean_object* v_res_1625_; 
v_sz_boxed_1623_ = lean_unbox_usize(v_sz_1619_);
lean_dec(v_sz_1619_);
v_i_boxed_1624_ = lean_unbox_usize(v_i_1620_);
lean_dec(v_i_1620_);
v_res_1625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(v_sz_boxed_1623_, v_i_boxed_1624_, v_bs_1621_, v___y_1622_);
return v_res_1625_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1627_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_1628_ = lean_unsigned_to_nat(15u);
v___x_1629_ = lean_unsigned_to_nat(238u);
v___x_1630_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0));
v___x_1631_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_1632_ = l_mkPanicMessageWithDecl(v___x_1631_, v___x_1630_, v___x_1629_, v___x_1628_, v___x_1627_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(lean_object* v___f_1633_, lean_object* v_fst_1634_, lean_object* v_fst_1635_, lean_object* v_fst_1636_, lean_object* v_fst_1637_, lean_object* v_snd_1638_, lean_object* v_x_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1);
v___x_1646_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(v___x_1645_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1648_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v___x_1646_, 1);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
lean_inc(v___y_1641_);
lean_inc_ref(v___y_1640_);
v___x_1648_ = lean_apply_11(v___f_1633_, v_a_1647_, v_fst_1634_, v_fst_1635_, v_fst_1636_, v_fst_1637_, v_snd_1638_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, lean_box(0));
return v___x_1648_;
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_snd_1638_);
lean_dec(v_fst_1637_);
lean_dec(v_fst_1636_);
lean_dec(v_fst_1635_);
lean_dec(v_fst_1634_);
lean_dec_ref(v___f_1633_);
v_a_1649_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1646_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1646_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___boxed(lean_object* v___f_1657_, lean_object* v_fst_1658_, lean_object* v_fst_1659_, lean_object* v_fst_1660_, lean_object* v_fst_1661_, lean_object* v_snd_1662_, lean_object* v_x_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1657_, v_fst_1658_, v_fst_1659_, v_fst_1660_, v_fst_1661_, v_snd_1662_, v_x_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec_ref(v_x_1663_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(lean_object* v_fst_1670_, lean_object* v_ctorField_1671_, lean_object* v_nextIdx_1672_, uint8_t v_has1BScalar_1673_, uint8_t v_has2BScalar_1674_, uint8_t v_has4BScalar_1675_, uint8_t v_has8BScalar_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1682_ = lean_array_push(v_fst_1670_, v_ctorField_1671_);
v___x_1683_ = lean_box(v_has4BScalar_1675_);
v___x_1684_ = lean_box(v_has8BScalar_1676_);
v___x_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = lean_box(v_has2BScalar_1674_);
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v___x_1685_);
v___x_1688_ = lean_box(v_has1BScalar_1673_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
lean_ctor_set(v___x_1689_, 1, v___x_1687_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v_nextIdx_1672_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1682_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0___boxed(lean_object* v_fst_1694_, lean_object* v_ctorField_1695_, lean_object* v_nextIdx_1696_, lean_object* v_has1BScalar_1697_, lean_object* v_has2BScalar_1698_, lean_object* v_has4BScalar_1699_, lean_object* v_has8BScalar_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
uint8_t v_has1BScalar_boxed_1706_; uint8_t v_has2BScalar_boxed_1707_; uint8_t v_has4BScalar_boxed_1708_; uint8_t v_has8BScalar_boxed_1709_; lean_object* v_res_1710_; 
v_has1BScalar_boxed_1706_ = lean_unbox(v_has1BScalar_1697_);
v_has2BScalar_boxed_1707_ = lean_unbox(v_has2BScalar_1698_);
v_has4BScalar_boxed_1708_ = lean_unbox(v_has4BScalar_1699_);
v_has8BScalar_boxed_1709_ = lean_unbox(v_has8BScalar_1700_);
v_res_1710_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1694_, v_ctorField_1695_, v_nextIdx_1696_, v_has1BScalar_boxed_1706_, v_has2BScalar_boxed_1707_, v_has4BScalar_boxed_1708_, v_has8BScalar_boxed_1709_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(lean_object* v_fst_1711_, lean_object* v___x_1712_, lean_object* v_a_1713_, lean_object* v___f_1714_, lean_object* v_fst_1715_, lean_object* v_fst_1716_, lean_object* v_fst_1717_, lean_object* v_snd_1718_, lean_object* v_00___1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_nat_add(v_fst_1711_, v___x_1712_);
v___x_1726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1726_, 0, v_fst_1711_);
lean_ctor_set(v___x_1726_, 1, v_a_1713_);
lean_inc(v___y_1723_);
lean_inc_ref(v___y_1722_);
lean_inc(v___y_1721_);
lean_inc_ref(v___y_1720_);
v___x_1727_ = lean_apply_11(v___f_1714_, v___x_1726_, v___x_1725_, v_fst_1715_, v_fst_1716_, v_fst_1717_, v_snd_1718_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, lean_box(0));
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2___boxed(lean_object* v_fst_1728_, lean_object* v___x_1729_, lean_object* v_a_1730_, lean_object* v___f_1731_, lean_object* v_fst_1732_, lean_object* v_fst_1733_, lean_object* v_fst_1734_, lean_object* v_snd_1735_, lean_object* v_00___1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1728_, v___x_1729_, v_a_1730_, v___f_1731_, v_fst_1732_, v_fst_1733_, v_fst_1734_, v_snd_1735_, v_00___1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___x_1729_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(lean_object* v_a_1745_, lean_object* v_b_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_array_1752_; lean_object* v_start_1753_; lean_object* v_stop_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1979_; 
v_array_1752_ = lean_ctor_get(v_a_1745_, 0);
v_start_1753_ = lean_ctor_get(v_a_1745_, 1);
v_stop_1754_ = lean_ctor_get(v_a_1745_, 2);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_a_1745_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1756_ = v_a_1745_;
v_isShared_1757_ = v_isSharedCheck_1979_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_stop_1754_);
lean_inc(v_start_1753_);
lean_inc(v_array_1752_);
lean_dec(v_a_1745_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1979_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_nat_dec_lt(v_start_1753_, v_stop_1754_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; 
lean_del_object(v___x_1756_);
lean_dec(v_stop_1754_);
lean_dec(v_start_1753_);
lean_dec_ref(v_array_1752_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v_b_1746_);
return v___x_1759_;
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = lean_array_fget_borrowed(v_array_1752_, v_start_1753_);
v___x_1761_ = l_Lean_Expr_fvarId_x21(v___x_1760_);
v___x_1762_ = l_Lean_FVarId_getType___redArg(v___x_1761_, v___y_1747_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = l_Lean_Compiler_LCNF_toLCNFType(v_a_1763_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = l_Lean_Compiler_LCNF_toMonoType(v_a_1765_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = l_Lean_Compiler_LCNF_toImpureType(v_a_1767_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_snd_1769_; lean_object* v_snd_1770_; lean_object* v_snd_1771_; lean_object* v_snd_1772_; lean_object* v_a_1773_; lean_object* v_fst_1774_; lean_object* v_fst_1775_; lean_object* v_fst_1776_; lean_object* v_fst_1777_; lean_object* v_fst_1778_; lean_object* v_snd_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1783_; 
v_snd_1769_ = lean_ctor_get(v_b_1746_, 1);
lean_inc(v_snd_1769_);
v_snd_1770_ = lean_ctor_get(v_snd_1769_, 1);
lean_inc(v_snd_1770_);
v_snd_1771_ = lean_ctor_get(v_snd_1770_, 1);
lean_inc(v_snd_1771_);
v_snd_1772_ = lean_ctor_get(v_snd_1771_, 1);
lean_inc(v_snd_1772_);
v_a_1773_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1768_, 1);
v_fst_1774_ = lean_ctor_get(v_b_1746_, 0);
lean_inc(v_fst_1774_);
lean_dec_ref(v_b_1746_);
v_fst_1775_ = lean_ctor_get(v_snd_1769_, 0);
lean_inc(v_fst_1775_);
lean_dec(v_snd_1769_);
v_fst_1776_ = lean_ctor_get(v_snd_1770_, 0);
lean_inc(v_fst_1776_);
lean_dec(v_snd_1770_);
v_fst_1777_ = lean_ctor_get(v_snd_1771_, 0);
lean_inc(v_fst_1777_);
lean_dec(v_snd_1771_);
v_fst_1778_ = lean_ctor_get(v_snd_1772_, 0);
lean_inc(v_fst_1778_);
v_snd_1779_ = lean_ctor_get(v_snd_1772_, 1);
lean_inc(v_snd_1779_);
lean_dec(v_snd_1772_);
v___x_1780_ = lean_unsigned_to_nat(1u);
v___x_1781_ = lean_nat_add(v_start_1753_, v___x_1780_);
lean_dec(v_start_1753_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v___x_1781_);
v___x_1783_ = v___x_1756_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_array_1752_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1946_, 2, v_stop_1754_);
v___x_1783_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___y_1785_; lean_object* v___f_1805_; 
lean_inc(v_fst_1774_);
v___f_1805_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1805_, 0, v_fst_1774_);
if (lean_obj_tag(v_a_1773_) == 4)
{
lean_object* v_declName_1806_; 
v_declName_1806_ = lean_ctor_get(v_a_1773_, 0);
if (lean_obj_tag(v_declName_1806_) == 1)
{
lean_object* v_pre_1807_; 
v_pre_1807_ = lean_ctor_get(v_declName_1806_, 0);
if (lean_obj_tag(v_pre_1807_) == 0)
{
lean_object* v_us_1808_; lean_object* v_str_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v_us_1808_ = lean_ctor_get(v_a_1773_, 1);
v_str_1809_ = lean_ctor_get(v_declName_1806_, 1);
v___x_1810_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__0));
v___x_1811_ = lean_string_dec_eq(v_str_1809_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__0));
v___x_1813_ = lean_string_dec_eq(v_str_1809_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__10));
v___x_1815_ = lean_string_dec_eq(v_str_1809_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__1));
v___x_1818_ = lean_string_dec_eq(v_str_1809_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1819_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__4));
v___x_1820_ = lean_string_dec_eq(v_str_1809_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__6));
v___x_1822_ = lean_string_dec_eq(v_str_1809_, v___x_1821_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1823_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9));
v___x_1824_ = lean_string_dec_eq(v_str_1809_, v___x_1823_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6));
v___x_1826_ = lean_string_dec_eq(v_str_1809_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1827_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3));
v___x_1828_ = lean_string_dec_eq(v_str_1809_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1829_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__0));
v___x_1830_ = lean_string_dec_eq(v_str_1809_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1831_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__3));
v___x_1832_ = lean_string_dec_eq(v_str_1809_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__2));
v___x_1834_ = lean_string_dec_eq(v_str_1809_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
lean_dec(v_fst_1774_);
v___x_1835_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v_a_1773_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref_known(v_a_1773_, 2);
v___y_1785_ = v___x_1835_;
goto v___jp_1784_;
}
else
{
lean_inc(v_pre_1807_);
lean_inc(v_us_1808_);
lean_dec_ref_known(v_a_1773_, 2);
if (lean_obj_tag(v_us_1808_) == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; uint8_t v___x_1841_; uint8_t v___x_1842_; lean_object* v___x_1843_; 
lean_dec_ref(v___f_1805_);
lean_dec(v_snd_1779_);
v___x_1836_ = lean_unsigned_to_nat(8u);
v___x_1837_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__20));
v___x_1838_ = l_Lean_Expr_const___override(v___x_1837_, v_us_1808_);
v___x_1839_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1836_);
lean_ctor_set(v___x_1839_, 1, v___x_1816_);
lean_ctor_set(v___x_1839_, 2, v___x_1838_);
v___x_1840_ = lean_unbox(v_fst_1776_);
lean_dec(v_fst_1776_);
v___x_1841_ = lean_unbox(v_fst_1777_);
lean_dec(v_fst_1777_);
v___x_1842_ = lean_unbox(v_fst_1778_);
lean_dec(v_fst_1778_);
v___x_1843_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1774_, v___x_1839_, v_fst_1775_, v___x_1840_, v___x_1841_, v___x_1842_, v___x_1834_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1785_ = v___x_1843_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec(v_fst_1774_);
v___x_1844_ = l_Lean_Name_str___override(v_pre_1807_, v___x_1833_);
v___x_1845_ = l_Lean_Expr_const___override(v___x_1844_, v_us_1808_);
v___x_1846_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1845_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___x_1845_);
v___y_1785_ = v___x_1846_;
goto v___jp_1784_;
}
}
}
else
{
lean_inc(v_pre_1807_);
lean_inc(v_us_1808_);
lean_dec_ref_known(v_a_1773_, 2);
if (lean_obj_tag(v_us_1808_) == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; uint8_t v___x_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; 
lean_dec_ref(v___f_1805_);
lean_dec(v_fst_1778_);
v___x_1847_ = lean_unsigned_to_nat(4u);
v___x_1848_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__17));
v___x_1849_ = l_Lean_Expr_const___override(v___x_1848_, v_us_1808_);
v___x_1850_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1847_);
lean_ctor_set(v___x_1850_, 1, v___x_1816_);
lean_ctor_set(v___x_1850_, 2, v___x_1849_);
v___x_1851_ = lean_unbox(v_fst_1776_);
lean_dec(v_fst_1776_);
v___x_1852_ = lean_unbox(v_fst_1777_);
lean_dec(v_fst_1777_);
v___x_1853_ = lean_unbox(v_snd_1779_);
lean_dec(v_snd_1779_);
v___x_1854_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1774_, v___x_1850_, v_fst_1775_, v___x_1851_, v___x_1852_, v___x_1832_, v___x_1853_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1785_ = v___x_1854_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec(v_fst_1774_);
v___x_1855_ = l_Lean_Name_str___override(v_pre_1807_, v___x_1831_);
v___x_1856_ = l_Lean_Expr_const___override(v___x_1855_, v_us_1808_);
v___x_1857_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1856_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___x_1856_);
v___y_1785_ = v___x_1857_;
goto v___jp_1784_;
}
}
}
else
{
lean_inc(v_pre_1807_);
lean_inc(v_us_1808_);
lean_dec_ref_known(v_a_1773_, 2);
if (lean_obj_tag(v_us_1808_) == 0)
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; uint8_t v___x_1863_; uint8_t v___x_1864_; lean_object* v___x_1865_; 
lean_dec_ref(v___f_1805_);
lean_dec(v_snd_1779_);
v___x_1858_ = lean_unsigned_to_nat(8u);
v___x_1859_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__26));
v___x_1860_ = l_Lean_Expr_const___override(v___x_1859_, v_us_1808_);
v___x_1861_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1858_);
lean_ctor_set(v___x_1861_, 1, v___x_1816_);
lean_ctor_set(v___x_1861_, 2, v___x_1860_);
v___x_1862_ = lean_unbox(v_fst_1776_);
lean_dec(v_fst_1776_);
v___x_1863_ = lean_unbox(v_fst_1777_);
lean_dec(v_fst_1777_);
v___x_1864_ = lean_unbox(v_fst_1778_);
lean_dec(v_fst_1778_);
v___x_1865_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1774_, v___x_1861_, v_fst_1775_, v___x_1862_, v___x_1863_, v___x_1864_, v___x_1830_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1785_ = v___x_1865_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_dec(v_fst_1774_);
v___x_1866_ = l_Lean_Name_str___override(v_pre_1807_, v___x_1829_);
v___x_1867_ = l_Lean_Expr_const___override(v___x_1866_, v_us_1808_);
v___x_1868_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1867_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___x_1867_);
v___y_1785_ = v___x_1868_;
goto v___jp_1784_;
}
}
}
else
{
lean_inc(v_pre_1807_);
lean_inc(v_us_1808_);
lean_dec_ref_known(v_a_1773_, 2);
if (lean_obj_tag(v_us_1808_) == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; uint8_t v___x_1874_; uint8_t v___x_1875_; lean_object* v___x_1876_; 
lean_dec_ref(v___f_1805_);
lean_dec(v_fst_1778_);
v___x_1869_ = lean_unsigned_to_nat(4u);
v___x_1870_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__4));
v___x_1871_ = l_Lean_Expr_const___override(v___x_1870_, v_us_1808_);
v___x_1872_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1869_);
lean_ctor_set(v___x_1872_, 1, v___x_1816_);
lean_ctor_set(v___x_1872_, 2, v___x_1871_);
v___x_1873_ = lean_unbox(v_fst_1776_);
lean_dec(v_fst_1776_);
v___x_1874_ = lean_unbox(v_fst_1777_);
lean_dec(v_fst_1777_);
v___x_1875_ = lean_unbox(v_snd_1779_);
lean_dec(v_snd_1779_);
v___x_1876_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1774_, v___x_1872_, v_fst_1775_, v___x_1873_, v___x_1874_, v___x_1828_, v___x_1875_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1785_ = v___x_1876_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
lean_dec(v_fst_1774_);
v___x_1877_ = l_Lean_Name_str___override(v_pre_1807_, v___x_1827_);
v___x_1878_ = l_Lean_Expr_const___override(v___x_1877_, v_us_1808_);
v___x_1879_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1878_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___x_1878_);
v___y_1785_ = v___x_1879_;
goto v___jp_1784_;
}
}
}
else
{
lean_inc(v_pre_1807_);
lean_inc(v_us_1808_);
lean_dec_ref_known(v_a_1773_, 2);
if (lean_obj_tag(v_us_1808_) == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; uint8_t v___x_1885_; uint8_t v___x_1886_; lean_object* v___x_1887_; 
lean_dec_ref(v___f_1805_);
lean_dec(v_fst_1777_);
v___x_1880_ = lean_unsigned_to_nat(2u);
v___x_1881_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__7));
v___x_1882_ = l_Lean_Expr_const___override(v___x_1881_, v_us_1808_);
v___x_1883_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1880_);
lean_ctor_set(v___x_1883_, 1, v___x_1816_);
lean_ctor_set(v___x_1883_, 2, v___x_1882_);
v___x_1884_ = lean_unbox(v_fst_1776_);
lean_dec(v_fst_1776_);
v___x_1885_ = lean_unbox(v_fst_1778_);
lean_dec(v_fst_1778_);
v___x_1886_ = lean_unbox(v_snd_1779_);
lean_dec(v_snd_1779_);
v___x_1887_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1774_, v___x_1883_, v_fst_1775_, v___x_1884_, v___x_1826_, v___x_1885_, v___x_1886_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1785_ = v___x_1887_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec(v_fst_1774_);
v___x_1888_ = l_Lean_Name_str___override(v_pre_1807_, v___x_1825_);
v___x_1889_ = l_Lean_Expr_const___override(v___x_1888_, v_us_1808_);
v___x_1890_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1889_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___x_1889_);
v___y_1785_ = v___x_1890_;
goto v___jp_1784_;
}
}
}
else
{
lean_inc(v_pre_1807_);
lean_inc(v_us_1808_);
lean_dec_ref_known(v_a_1773_, 2);
if (lean_obj_tag(v_us_1808_) == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; uint8_t v___x_1895_; uint8_t v___x_1896_; lean_object* v___x_1897_; 
lean_dec_ref(v___f_1805_);
lean_dec(v_fst_1776_);
v___x_1891_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__10));
v___x_1892_ = l_Lean_Expr_const___override(v___x_1891_, v_us_1808_);
v___x_1893_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1780_);
lean_ctor_set(v___x_1893_, 1, v___x_1816_);
lean_ctor_set(v___x_1893_, 2, v___x_1892_);
v___x_1894_ = lean_unbox(v_fst_1777_);
lean_dec(v_fst_1777_);
v___x_1895_ = lean_unbox(v_fst_1778_);
lean_dec(v_fst_1778_);
v___x_1896_ = lean_unbox(v_snd_1779_);
lean_dec(v_snd_1779_);
v___x_1897_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1774_, v___x_1893_, v_fst_1775_, v___x_1824_, v___x_1894_, v___x_1895_, v___x_1896_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1785_ = v___x_1897_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
lean_dec(v_fst_1774_);
v___x_1898_ = l_Lean_Name_str___override(v_pre_1807_, v___x_1823_);
v___x_1899_ = l_Lean_Expr_const___override(v___x_1898_, v_us_1808_);
v___x_1900_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1899_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___x_1899_);
v___y_1785_ = v___x_1900_;
goto v___jp_1784_;
}
}
}
else
{
lean_inc(v_pre_1807_);
lean_inc(v_us_1808_);
lean_dec_ref_known(v_a_1773_, 2);
if (lean_obj_tag(v_us_1808_) == 0)
{
lean_object* v___x_1901_; uint8_t v___x_1902_; uint8_t v___x_1903_; uint8_t v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; 
lean_dec_ref(v___f_1805_);
v___x_1901_ = lean_box(4);
v___x_1902_ = lean_unbox(v_fst_1776_);
lean_dec(v_fst_1776_);
v___x_1903_ = lean_unbox(v_fst_1777_);
lean_dec(v_fst_1777_);
v___x_1904_ = lean_unbox(v_fst_1778_);
lean_dec(v_fst_1778_);
v___x_1905_ = lean_unbox(v_snd_1779_);
lean_dec(v_snd_1779_);
v___x_1906_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1774_, v___x_1901_, v_fst_1775_, v___x_1902_, v___x_1903_, v___x_1904_, v___x_1905_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1785_ = v___x_1906_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec(v_fst_1774_);
v___x_1907_ = l_Lean_Name_str___override(v_pre_1807_, v___x_1821_);
v___x_1908_ = l_Lean_Expr_const___override(v___x_1907_, v_us_1808_);
v___x_1909_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1908_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___x_1908_);
v___y_1785_ = v___x_1909_;
goto v___jp_1784_;
}
}
}
else
{
lean_inc(v_pre_1807_);
lean_inc(v_us_1808_);
lean_dec_ref_known(v_a_1773_, 2);
if (lean_obj_tag(v_us_1808_) == 0)
{
lean_object* v___x_1910_; uint8_t v___x_1911_; uint8_t v___x_1912_; uint8_t v___x_1913_; uint8_t v___x_1914_; lean_object* v___x_1915_; 
lean_dec_ref(v___f_1805_);
v___x_1910_ = lean_box(0);
v___x_1911_ = lean_unbox(v_fst_1776_);
lean_dec(v_fst_1776_);
v___x_1912_ = lean_unbox(v_fst_1777_);
lean_dec(v_fst_1777_);
v___x_1913_ = lean_unbox(v_fst_1778_);
lean_dec(v_fst_1778_);
v___x_1914_ = lean_unbox(v_snd_1779_);
lean_dec(v_snd_1779_);
v___x_1915_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1774_, v___x_1910_, v_fst_1775_, v___x_1911_, v___x_1912_, v___x_1913_, v___x_1914_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1785_ = v___x_1915_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_dec(v_fst_1774_);
v___x_1916_ = l_Lean_Name_str___override(v_pre_1807_, v___x_1819_);
v___x_1917_ = l_Lean_Expr_const___override(v___x_1916_, v_us_1808_);
v___x_1918_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1917_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___x_1917_);
v___y_1785_ = v___x_1918_;
goto v___jp_1784_;
}
}
}
else
{
lean_inc(v_pre_1807_);
lean_inc(v_us_1808_);
lean_dec_ref_known(v_a_1773_, 2);
if (lean_obj_tag(v_us_1808_) == 0)
{
lean_object* v___x_1919_; uint8_t v___x_1920_; uint8_t v___x_1921_; uint8_t v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; 
lean_dec_ref(v___f_1805_);
v___x_1919_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___closed__0));
v___x_1920_ = lean_unbox(v_fst_1776_);
lean_dec(v_fst_1776_);
v___x_1921_ = lean_unbox(v_fst_1777_);
lean_dec(v_fst_1777_);
v___x_1922_ = lean_unbox(v_fst_1778_);
lean_dec(v_fst_1778_);
v___x_1923_ = lean_unbox(v_snd_1779_);
lean_dec(v_snd_1779_);
v___x_1924_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1774_, v___x_1919_, v_fst_1775_, v___x_1920_, v___x_1921_, v___x_1922_, v___x_1923_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1785_ = v___x_1924_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec(v_fst_1774_);
v___x_1925_ = l_Lean_Name_str___override(v_pre_1807_, v___x_1817_);
v___x_1926_ = l_Lean_Expr_const___override(v___x_1925_, v_us_1808_);
v___x_1927_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1926_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___x_1926_);
v___y_1785_ = v___x_1927_;
goto v___jp_1784_;
}
}
}
else
{
lean_dec(v_fst_1774_);
if (lean_obj_tag(v_us_1808_) == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_box(0);
v___x_1929_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1775_, v___x_1780_, v_a_1773_, v___f_1805_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1928_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1785_ = v___x_1929_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_inc(v_pre_1807_);
lean_inc(v_us_1808_);
lean_dec_ref_known(v_a_1773_, 2);
v___x_1930_ = l_Lean_Name_str___override(v_pre_1807_, v___x_1814_);
v___x_1931_ = l_Lean_Expr_const___override(v___x_1930_, v_us_1808_);
v___x_1932_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1931_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___x_1931_);
v___y_1785_ = v___x_1932_;
goto v___jp_1784_;
}
}
}
else
{
lean_dec(v_fst_1774_);
if (lean_obj_tag(v_us_1808_) == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_box(0);
v___x_1934_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1775_, v___x_1780_, v_a_1773_, v___f_1805_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1933_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1785_ = v___x_1934_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_inc(v_pre_1807_);
lean_inc(v_us_1808_);
lean_dec_ref_known(v_a_1773_, 2);
v___x_1935_ = l_Lean_Name_str___override(v_pre_1807_, v___x_1812_);
v___x_1936_ = l_Lean_Expr_const___override(v___x_1935_, v_us_1808_);
v___x_1937_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1936_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___x_1936_);
v___y_1785_ = v___x_1937_;
goto v___jp_1784_;
}
}
}
else
{
lean_dec(v_fst_1774_);
if (lean_obj_tag(v_us_1808_) == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = lean_box(0);
v___x_1939_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1775_, v___x_1780_, v_a_1773_, v___f_1805_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1938_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1785_ = v___x_1939_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
lean_inc(v_pre_1807_);
lean_inc(v_us_1808_);
lean_dec_ref_known(v_a_1773_, 2);
v___x_1940_ = l_Lean_Name_str___override(v_pre_1807_, v___x_1810_);
v___x_1941_ = l_Lean_Expr_const___override(v___x_1940_, v_us_1808_);
v___x_1942_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v___x_1941_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___x_1941_);
v___y_1785_ = v___x_1942_;
goto v___jp_1784_;
}
}
}
else
{
lean_object* v___x_1943_; 
lean_dec(v_fst_1774_);
v___x_1943_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v_a_1773_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref_known(v_a_1773_, 2);
v___y_1785_ = v___x_1943_;
goto v___jp_1784_;
}
}
else
{
lean_object* v___x_1944_; 
lean_dec(v_fst_1774_);
v___x_1944_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v_a_1773_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref_known(v_a_1773_, 2);
v___y_1785_ = v___x_1944_;
goto v___jp_1784_;
}
}
else
{
lean_object* v___x_1945_; 
lean_dec(v_fst_1774_);
v___x_1945_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1805_, v_fst_1775_, v_fst_1776_, v_fst_1777_, v_fst_1778_, v_snd_1779_, v_a_1773_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v_a_1773_);
v___y_1785_ = v___x_1945_;
goto v___jp_1784_;
}
v___jp_1784_:
{
if (lean_obj_tag(v___y_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1796_; 
v_a_1786_ = lean_ctor_get(v___y_1785_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___y_1785_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1788_ = v___y_1785_;
v_isShared_1789_ = v_isSharedCheck_1796_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___y_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1796_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
if (lean_obj_tag(v_a_1786_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; 
lean_dec_ref(v___x_1783_);
v_a_1790_ = lean_ctor_get(v_a_1786_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v_a_1786_, 1);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v_a_1790_);
v___x_1792_ = v___x_1788_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
else
{
lean_object* v_a_1794_; 
lean_del_object(v___x_1788_);
v_a_1794_ = lean_ctor_get(v_a_1786_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v_a_1786_, 1);
v_a_1745_ = v___x_1783_;
v_b_1746_ = v_a_1794_;
goto _start;
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec_ref(v___x_1783_);
v_a_1797_ = lean_ctor_get(v___y_1785_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___y_1785_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___y_1785_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___y_1785_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_del_object(v___x_1756_);
lean_dec(v_stop_1754_);
lean_dec(v_start_1753_);
lean_dec_ref(v_array_1752_);
lean_dec_ref(v_b_1746_);
v_a_1947_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1768_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1768_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_del_object(v___x_1756_);
lean_dec(v_stop_1754_);
lean_dec(v_start_1753_);
lean_dec_ref(v_array_1752_);
lean_dec_ref(v_b_1746_);
v_a_1955_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1766_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1766_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_del_object(v___x_1756_);
lean_dec(v_stop_1754_);
lean_dec(v_start_1753_);
lean_dec_ref(v_array_1752_);
lean_dec_ref(v_b_1746_);
v_a_1963_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1764_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1764_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_del_object(v___x_1756_);
lean_dec(v_stop_1754_);
lean_dec(v_start_1753_);
lean_dec_ref(v_array_1752_);
lean_dec_ref(v_b_1746_);
v_a_1971_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1762_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1762_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___boxed(lean_object* v_a_1980_, lean_object* v_b_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v_a_1980_, v_b_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1(lean_object* v_numFields_1988_, lean_object* v_numParams_1989_, uint8_t v___x_1990_, lean_object* v_ctorName_1991_, lean_object* v_cidx_1992_, lean_object* v___f_1993_, lean_object* v_params_1994_, lean_object* v_x_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2001_ = lean_mk_empty_array_with_capacity(v_numFields_1988_);
v___x_2002_ = lean_unsigned_to_nat(0u);
v___x_2003_ = lean_nat_add(v_numParams_1989_, v_numFields_1988_);
v___x_2004_ = l_Array_toSubarray___redArg(v_params_1994_, v_numParams_1989_, v___x_2003_);
v___x_2005_ = lean_box(v___x_1990_);
v___x_2006_ = lean_box(v___x_1990_);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2005_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = lean_box(v___x_1990_);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
lean_ctor_set(v___x_2009_, 1, v___x_2007_);
v___x_2010_ = lean_box(v___x_1990_);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v___x_2009_);
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2002_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2001_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v___x_2004_, v___x_2013_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2078_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2078_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2078_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v_snd_2019_; lean_object* v_fst_2020_; lean_object* v_fst_2021_; lean_object* v_snd_2022_; size_t v_sz_2023_; size_t v___x_2024_; lean_object* v___x_2025_; lean_object* v_snd_2026_; lean_object* v_snd_2027_; lean_object* v_fst_2028_; lean_object* v_snd_2029_; lean_object* v_fst_2030_; lean_object* v_fst_2031_; lean_object* v_fst_2032_; lean_object* v_snd_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2077_; 
v_snd_2019_ = lean_ctor_get(v_a_2015_, 1);
lean_inc(v_snd_2019_);
v_fst_2020_ = lean_ctor_get(v_a_2015_, 0);
lean_inc(v_fst_2020_);
lean_dec(v_a_2015_);
v_fst_2021_ = lean_ctor_get(v_snd_2019_, 0);
lean_inc_n(v_fst_2021_, 2);
v_snd_2022_ = lean_ctor_get(v_snd_2019_, 1);
lean_inc(v_snd_2022_);
lean_dec(v_snd_2019_);
v_sz_2023_ = lean_array_size(v_fst_2020_);
v___x_2024_ = ((size_t)0ULL);
v___x_2025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(v_sz_2023_, v___x_2024_, v_fst_2020_, v_fst_2021_);
v_snd_2026_ = lean_ctor_get(v_snd_2022_, 1);
lean_inc(v_snd_2026_);
v_snd_2027_ = lean_ctor_get(v_snd_2026_, 1);
lean_inc(v_snd_2027_);
v_fst_2028_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_fst_2028_);
v_snd_2029_ = lean_ctor_get(v___x_2025_, 1);
lean_inc(v_snd_2029_);
lean_dec_ref(v___x_2025_);
v_fst_2030_ = lean_ctor_get(v_snd_2022_, 0);
lean_inc(v_fst_2030_);
lean_dec(v_snd_2022_);
v_fst_2031_ = lean_ctor_get(v_snd_2026_, 0);
lean_inc(v_fst_2031_);
lean_dec(v_snd_2026_);
v_fst_2032_ = lean_ctor_get(v_snd_2027_, 0);
v_snd_2033_ = lean_ctor_get(v_snd_2027_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_snd_2027_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2035_ = v_snd_2027_;
v_isShared_2036_ = v_isSharedCheck_2077_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_snd_2033_);
lean_inc(v_fst_2032_);
lean_dec(v_snd_2027_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2077_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v_fields_2039_; lean_object* v_nextOffset_2040_; lean_object* v_fields_2049_; lean_object* v_nextOffset_2050_; lean_object* v_fields_2057_; lean_object* v_nextOffset_2058_; lean_object* v_fields_2065_; lean_object* v_nextOffset_2066_; uint8_t v___x_2072_; 
v___x_2037_ = lean_nat_sub(v_snd_2029_, v_fst_2021_);
lean_dec(v_snd_2029_);
v___x_2072_ = lean_unbox(v_snd_2033_);
lean_dec(v_snd_2033_);
if (v___x_2072_ == 0)
{
v_fields_2065_ = v_fst_2028_;
v_nextOffset_2066_ = v___x_2002_;
goto v___jp_2064_;
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v_fst_2075_; lean_object* v_snd_2076_; 
v___x_2073_ = lean_unsigned_to_nat(8u);
lean_inc_ref(v___f_1993_);
v___x_2074_ = lean_apply_3(v___f_1993_, v_fst_2028_, v___x_2073_, v___x_2002_);
v_fst_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_fst_2075_);
v_snd_2076_ = lean_ctor_get(v___x_2074_, 1);
lean_inc(v_snd_2076_);
lean_dec_ref(v___x_2074_);
v_fields_2065_ = v_fst_2075_;
v_nextOffset_2066_ = v_snd_2076_;
goto v___jp_2064_;
}
v___jp_2038_:
{
lean_object* v___x_2041_; lean_object* v___x_2043_; 
v___x_2041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2041_, 0, v_ctorName_1991_);
lean_ctor_set(v___x_2041_, 1, v_cidx_1992_);
lean_ctor_set(v___x_2041_, 2, v_fst_2021_);
lean_ctor_set(v___x_2041_, 3, v___x_2037_);
lean_ctor_set(v___x_2041_, 4, v_nextOffset_2040_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v_fields_2039_);
lean_ctor_set(v___x_2035_, 0, v___x_2041_);
v___x_2043_ = v___x_2035_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_fields_2039_);
v___x_2043_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2045_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2043_);
v___x_2045_ = v___x_2017_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
v___jp_2048_:
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_unbox(v_fst_2030_);
lean_dec(v_fst_2030_);
if (v___x_2051_ == 0)
{
lean_dec_ref(v___f_1993_);
v_fields_2039_ = v_fields_2049_;
v_nextOffset_2040_ = v_nextOffset_2050_;
goto v___jp_2038_;
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v_fst_2054_; lean_object* v_snd_2055_; 
v___x_2052_ = lean_unsigned_to_nat(1u);
v___x_2053_ = lean_apply_3(v___f_1993_, v_fields_2049_, v___x_2052_, v_nextOffset_2050_);
v_fst_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_fst_2054_);
v_snd_2055_ = lean_ctor_get(v___x_2053_, 1);
lean_inc(v_snd_2055_);
lean_dec_ref(v___x_2053_);
v_fields_2039_ = v_fst_2054_;
v_nextOffset_2040_ = v_snd_2055_;
goto v___jp_2038_;
}
}
v___jp_2056_:
{
uint8_t v___x_2059_; 
v___x_2059_ = lean_unbox(v_fst_2031_);
lean_dec(v_fst_2031_);
if (v___x_2059_ == 0)
{
v_fields_2049_ = v_fields_2057_;
v_nextOffset_2050_ = v_nextOffset_2058_;
goto v___jp_2048_;
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v_fst_2062_; lean_object* v_snd_2063_; 
v___x_2060_ = lean_unsigned_to_nat(2u);
lean_inc_ref(v___f_1993_);
v___x_2061_ = lean_apply_3(v___f_1993_, v_fields_2057_, v___x_2060_, v_nextOffset_2058_);
v_fst_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_fst_2062_);
v_snd_2063_ = lean_ctor_get(v___x_2061_, 1);
lean_inc(v_snd_2063_);
lean_dec_ref(v___x_2061_);
v_fields_2049_ = v_fst_2062_;
v_nextOffset_2050_ = v_snd_2063_;
goto v___jp_2048_;
}
}
v___jp_2064_:
{
uint8_t v___x_2067_; 
v___x_2067_ = lean_unbox(v_fst_2032_);
lean_dec(v_fst_2032_);
if (v___x_2067_ == 0)
{
v_fields_2057_ = v_fields_2065_;
v_nextOffset_2058_ = v_nextOffset_2066_;
goto v___jp_2056_;
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v_fst_2070_; lean_object* v_snd_2071_; 
v___x_2068_ = lean_unsigned_to_nat(4u);
lean_inc_ref(v___f_1993_);
v___x_2069_ = lean_apply_3(v___f_1993_, v_fields_2065_, v___x_2068_, v_nextOffset_2066_);
v_fst_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_fst_2070_);
v_snd_2071_ = lean_ctor_get(v___x_2069_, 1);
lean_inc(v_snd_2071_);
lean_dec_ref(v___x_2069_);
v_fields_2057_ = v_fst_2070_;
v_nextOffset_2058_ = v_snd_2071_;
goto v___jp_2056_;
}
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v___f_1993_);
lean_dec(v_cidx_1992_);
lean_dec(v_ctorName_1991_);
v_a_2079_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2014_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2014_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___boxed(lean_object* v_numFields_2087_, lean_object* v_numParams_2088_, lean_object* v___x_2089_, lean_object* v_ctorName_2090_, lean_object* v_cidx_2091_, lean_object* v___f_2092_, lean_object* v_params_2093_, lean_object* v_x_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
uint8_t v___x_13843__boxed_2100_; lean_object* v_res_2101_; 
v___x_13843__boxed_2100_ = lean_unbox(v___x_2089_);
v_res_2101_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1(v_numFields_2087_, v_numParams_2088_, v___x_13843__boxed_2100_, v_ctorName_2090_, v_cidx_2091_, v___f_2092_, v_params_2093_, v_x_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec_ref(v_x_2094_);
lean_dec(v_numFields_2087_);
return v_res_2101_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2102_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_2103_ = lean_unsigned_to_nat(66u);
v___x_2104_ = lean_unsigned_to_nat(199u);
v___x_2105_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0));
v___x_2106_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_2107_ = l_mkPanicMessageWithDecl(v___x_2106_, v___x_2105_, v___x_2104_, v___x_2103_, v___x_2102_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(lean_object* v_ctorName_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___x_2118_; lean_object* v_env_2119_; uint8_t v___x_2120_; lean_object* v___x_2121_; 
v___x_2118_ = lean_st_ref_get(v_a_2111_);
v_env_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc_ref(v_env_2119_);
lean_dec(v___x_2118_);
v___x_2120_ = 0;
lean_inc(v_ctorName_2109_);
v___x_2121_ = l_Lean_Environment_find_x3f(v_env_2119_, v_ctorName_2109_, v___x_2120_);
if (lean_obj_tag(v___x_2121_) == 1)
{
lean_object* v_val_2122_; 
v_val_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_val_2122_);
lean_dec_ref_known(v___x_2121_, 1);
if (lean_obj_tag(v_val_2122_) == 6)
{
lean_object* v_val_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v_toConstantVal_2127_; lean_object* v_cidx_2128_; lean_object* v_numParams_2129_; lean_object* v_numFields_2130_; lean_object* v_type_2131_; lean_object* v___f_2132_; lean_object* v___x_2133_; lean_object* v___f_2134_; lean_object* v___x_2135_; 
v_val_2123_ = lean_ctor_get(v_val_2122_, 0);
lean_inc_ref(v_val_2123_);
lean_dec_ref_known(v_val_2122_, 1);
v___x_2124_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13);
v___x_2125_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17);
v___x_2126_ = lean_st_mk_ref(v___x_2125_);
v_toConstantVal_2127_ = lean_ctor_get(v_val_2123_, 0);
lean_inc_ref(v_toConstantVal_2127_);
v_cidx_2128_ = lean_ctor_get(v_val_2123_, 2);
lean_inc(v_cidx_2128_);
v_numParams_2129_ = lean_ctor_get(v_val_2123_, 3);
lean_inc(v_numParams_2129_);
v_numFields_2130_ = lean_ctor_get(v_val_2123_, 4);
lean_inc(v_numFields_2130_);
lean_dec_ref(v_val_2123_);
v_type_2131_ = lean_ctor_get(v_toConstantVal_2127_, 2);
lean_inc_ref(v_type_2131_);
lean_dec_ref(v_toConstantVal_2127_);
v___f_2132_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__1));
v___x_2133_ = lean_box(v___x_2120_);
v___f_2134_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___boxed), 13, 6);
lean_closure_set(v___f_2134_, 0, v_numFields_2130_);
lean_closure_set(v___f_2134_, 1, v_numParams_2129_);
lean_closure_set(v___f_2134_, 2, v___x_2133_);
lean_closure_set(v___f_2134_, 3, v_ctorName_2109_);
lean_closure_set(v___f_2134_, 4, v_cidx_2128_);
lean_closure_set(v___f_2134_, 5, v___f_2132_);
v___x_2135_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg(v_type_2131_, v___f_2134_, v___x_2120_, v___x_2120_, v___x_2124_, v___x_2126_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2144_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = lean_st_ref_get(v___x_2126_);
lean_dec(v___x_2126_);
lean_dec(v___x_2140_);
if (v_isShared_2139_ == 0)
{
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2136_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
else
{
lean_dec(v___x_2126_);
return v___x_2135_;
}
}
else
{
lean_dec(v_val_2122_);
lean_dec(v_ctorName_2109_);
v___y_2114_ = v_a_2110_;
v___y_2115_ = v_a_2111_;
goto v___jp_2113_;
}
}
else
{
lean_dec(v___x_2121_);
lean_dec(v_ctorName_2109_);
v___y_2114_ = v_a_2110_;
v___y_2115_ = v_a_2111_;
goto v___jp_2113_;
}
v___jp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0);
v___x_2117_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(v___x_2116_, v___y_2114_, v___y_2115_);
return v___x_2117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___boxed(lean_object* v_ctorName_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(v_ctorName_2145_, v_a_2146_, v_a_2147_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3(lean_object* v_inst_2150_, lean_object* v_R_2151_, lean_object* v_a_2152_, lean_object* v_b_2153_, lean_object* v_c_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v_a_2152_, v_b_2153_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___boxed(lean_object* v_inst_2161_, lean_object* v_R_2162_, lean_object* v_a_2163_, lean_object* v_b_2164_, lean_object* v_c_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3(v_inst_2161_, v_R_2162_, v_a_2163_, v_b_2164_, v_c_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setCtorLayout(lean_object* v_ctorName_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_){
_start:
{
lean_object* v___x_2176_; lean_object* v_env_2177_; lean_object* v___x_2178_; lean_object* v_toEnvExtension_2179_; lean_object* v_asyncMode_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; lean_object* v___x_2183_; 
v___x_2176_ = lean_st_ref_get(v_a_2174_);
v_env_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc_ref(v_env_2177_);
lean_dec(v___x_2176_);
v___x_2178_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt;
v_toEnvExtension_2179_ = lean_ctor_get(v___x_2178_, 0);
v_asyncMode_2180_ = lean_ctor_get(v_toEnvExtension_2179_, 2);
v___x_2181_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
v___x_2182_ = 0;
lean_inc(v_ctorName_2172_);
v___x_2183_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2181_, v___x_2178_, v_env_2177_, v_ctorName_2172_, v_asyncMode_2180_, v___x_2182_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v___x_2184_; 
lean_inc(v_ctorName_2172_);
v___x_2184_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(v_ctorName_2172_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2186_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc_n(v_a_2185_, 2);
lean_dec_ref_known(v___x_2184_, 1);
v___x_2186_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout(v_a_2185_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2214_; 
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; 
v_unused_2215_ = lean_ctor_get(v___x_2186_, 0);
lean_dec(v_unused_2215_);
v___x_2188_ = v___x_2186_;
v_isShared_2189_ = v_isSharedCheck_2214_;
goto v_resetjp_2187_;
}
else
{
lean_dec(v___x_2186_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2214_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; lean_object* v_env_2191_; lean_object* v_nextMacroScope_2192_; lean_object* v_ngen_2193_; lean_object* v_auxDeclNGen_2194_; lean_object* v_traceState_2195_; lean_object* v_messages_2196_; lean_object* v_infoState_2197_; lean_object* v_snapshotTasks_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2212_; 
v___x_2190_ = lean_st_ref_take(v_a_2174_);
v_env_2191_ = lean_ctor_get(v___x_2190_, 0);
v_nextMacroScope_2192_ = lean_ctor_get(v___x_2190_, 1);
v_ngen_2193_ = lean_ctor_get(v___x_2190_, 2);
v_auxDeclNGen_2194_ = lean_ctor_get(v___x_2190_, 3);
v_traceState_2195_ = lean_ctor_get(v___x_2190_, 4);
v_messages_2196_ = lean_ctor_get(v___x_2190_, 6);
v_infoState_2197_ = lean_ctor_get(v___x_2190_, 7);
v_snapshotTasks_2198_ = lean_ctor_get(v___x_2190_, 8);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v___x_2190_, 5);
lean_dec(v_unused_2213_);
v___x_2200_ = v___x_2190_;
v_isShared_2201_ = v_isSharedCheck_2212_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_snapshotTasks_2198_);
lean_inc(v_infoState_2197_);
lean_inc(v_messages_2196_);
lean_inc(v_traceState_2195_);
lean_inc(v_auxDeclNGen_2194_);
lean_inc(v_ngen_2193_);
lean_inc(v_nextMacroScope_2192_);
lean_inc(v_env_2191_);
lean_dec(v___x_2190_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2212_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2202_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2178_, v_env_2191_, v_ctorName_2172_, v_a_2185_);
v___x_2203_ = lean_obj_once(&l_Lean_Compiler_LCNF_setImpureType___closed__2, &l_Lean_Compiler_LCNF_setImpureType___closed__2_once, _init_l_Lean_Compiler_LCNF_setImpureType___closed__2);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 5, v___x_2203_);
lean_ctor_set(v___x_2200_, 0, v___x_2202_);
v___x_2205_ = v___x_2200_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2202_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_nextMacroScope_2192_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_ngen_2193_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_auxDeclNGen_2194_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v_traceState_2195_);
lean_ctor_set(v_reuseFailAlloc_2211_, 5, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2211_, 6, v_messages_2196_);
lean_ctor_set(v_reuseFailAlloc_2211_, 7, v_infoState_2197_);
lean_ctor_set(v_reuseFailAlloc_2211_, 8, v_snapshotTasks_2198_);
v___x_2205_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2206_ = lean_st_ref_put(v_a_2174_, v___x_2205_);
v___x_2207_ = lean_box(0);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2207_);
v___x_2209_ = v___x_2188_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
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
else
{
lean_dec(v_a_2185_);
lean_dec(v_ctorName_2172_);
return v___x_2186_;
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_ctorName_2172_);
v_a_2216_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2184_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2184_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_ctorName_2172_);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2231_ == 0)
{
lean_object* v_unused_2232_; 
v_unused_2232_ = lean_ctor_get(v___x_2183_, 0);
lean_dec(v_unused_2232_);
v___x_2225_ = v___x_2183_;
v_isShared_2226_ = v_isSharedCheck_2231_;
goto v_resetjp_2224_;
}
else
{
lean_dec(v___x_2183_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2231_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2227_ = lean_box(0);
if (v_isShared_2226_ == 0)
{
lean_ctor_set_tag(v___x_2225_, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2227_);
v___x_2229_ = v___x_2225_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setCtorLayout___boxed(lean_object* v_ctorName_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_Compiler_LCNF_setCtorLayout(v_ctorName_2233_, v_a_2234_, v_a_2235_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getCtorLayout(lean_object* v_ctorName_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v_env_2243_; lean_object* v___x_2244_; lean_object* v_toEnvExtension_2245_; lean_object* v_asyncMode_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; 
v___x_2242_ = lean_st_ref_get(v_a_2240_);
v_env_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc_ref(v_env_2243_);
lean_dec(v___x_2242_);
v___x_2244_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt;
v_toEnvExtension_2245_ = lean_ctor_get(v___x_2244_, 0);
v_asyncMode_2246_ = lean_ctor_get(v_toEnvExtension_2245_, 2);
v___x_2247_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
v___x_2248_ = 0;
lean_inc(v_ctorName_2238_);
v___x_2249_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2247_, v___x_2244_, v_env_2243_, v_ctorName_2238_, v_asyncMode_2246_, v___x_2248_);
if (lean_obj_tag(v___x_2249_) == 1)
{
lean_object* v_val_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec(v_ctorName_2238_);
v_val_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_val_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
lean_ctor_set_tag(v___x_2252_, 0);
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_val_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec(v___x_2249_);
v___x_2258_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__1, &l_Lean_Compiler_LCNF_nameToImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1);
v___x_2259_ = l_Lean_MessageData_ofName(v_ctorName_2238_);
v___x_2260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__3, &l_Lean_Compiler_LCNF_nameToImpureType___closed__3_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__3);
v___x_2262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2260_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v___x_2262_, v_a_2239_, v_a_2240_);
return v___x_2263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getCtorLayout___boxed(lean_object* v_ctorName_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_2264_, v_a_2265_, v_a_2266_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(lean_object* v_as_2269_, size_t v_sz_2270_, size_t v_i_2271_, lean_object* v_b_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
uint8_t v___x_2276_; 
v___x_2276_ = lean_usize_dec_lt(v_i_2271_, v_sz_2270_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; 
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v_b_2272_);
return v___x_2277_;
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2279_; 
v_a_2278_ = lean_array_uget_borrowed(v_as_2269_, v_i_2271_);
lean_inc(v_a_2278_);
v___x_2279_ = l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(v_a_2278_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v___x_2280_; 
lean_dec_ref_known(v___x_2279_, 1);
lean_inc(v_a_2278_);
v___x_2280_ = l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f(v_a_2278_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v___x_2281_; size_t v___x_2282_; size_t v___x_2283_; 
lean_dec_ref_known(v___x_2280_, 1);
v___x_2281_ = lean_box(0);
v___x_2282_ = ((size_t)1ULL);
v___x_2283_ = lean_usize_add(v_i_2271_, v___x_2282_);
v_i_2271_ = v___x_2283_;
v_b_2272_ = v___x_2281_;
goto _start;
}
else
{
return v___x_2280_;
}
}
else
{
return v___x_2279_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2___boxed(lean_object* v_as_2285_, lean_object* v_sz_2286_, lean_object* v_i_2287_, lean_object* v_b_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
size_t v_sz_boxed_2292_; size_t v_i_boxed_2293_; lean_object* v_res_2294_; 
v_sz_boxed_2292_ = lean_unbox_usize(v_sz_2286_);
lean_dec(v_sz_2286_);
v_i_boxed_2293_ = lean_unbox_usize(v_i_2287_);
lean_dec(v_i_2287_);
v_res_2294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(v_as_2285_, v_sz_boxed_2292_, v_i_boxed_2293_, v_b_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v_as_2285_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(lean_object* v_as_x27_2295_, lean_object* v_b_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
if (lean_obj_tag(v_as_x27_2295_) == 0)
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v_b_2296_);
return v___x_2300_;
}
else
{
lean_object* v_head_2301_; lean_object* v_tail_2302_; lean_object* v___x_2303_; 
v_head_2301_ = lean_ctor_get(v_as_x27_2295_, 0);
v_tail_2302_ = lean_ctor_get(v_as_x27_2295_, 1);
lean_inc(v_head_2301_);
v___x_2303_ = l_Lean_Compiler_LCNF_setOtherDeclMonoType(v_head_2301_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v___x_2304_; 
lean_dec_ref_known(v___x_2303_, 1);
lean_inc(v_head_2301_);
v___x_2304_ = l_Lean_Compiler_LCNF_setCtorLayout(v_head_2301_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v___x_2305_; 
lean_dec_ref_known(v___x_2304_, 1);
v___x_2305_ = lean_box(0);
v_as_x27_2295_ = v_tail_2302_;
v_b_2296_ = v___x_2305_;
goto _start;
}
else
{
return v___x_2304_;
}
}
else
{
return v___x_2303_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg___boxed(lean_object* v_as_x27_2307_, lean_object* v_b_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(v_as_x27_2307_, v_b_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v_as_x27_2307_);
return v_res_2312_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_2315_ = l_Lean_stringToMessageData(v___x_2314_);
return v___x_2315_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_2318_ = l_Lean_stringToMessageData(v___x_2317_);
return v___x_2318_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_2321_ = l_Lean_stringToMessageData(v___x_2320_);
return v___x_2321_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_2324_ = l_Lean_stringToMessageData(v___x_2323_);
return v___x_2324_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_2327_ = l_Lean_stringToMessageData(v___x_2326_);
return v___x_2327_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_2330_ = l_Lean_stringToMessageData(v___x_2329_);
return v___x_2330_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_2333_ = l_Lean_stringToMessageData(v___x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2334_, lean_object* v_declHint_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; lean_object* v_env_2339_; uint8_t v___x_2340_; 
v___x_2338_ = lean_st_ref_get(v___y_2336_);
v_env_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc_ref(v_env_2339_);
lean_dec(v___x_2338_);
v___x_2340_ = l_Lean_Name_isAnonymous(v_declHint_2335_);
if (v___x_2340_ == 0)
{
uint8_t v_isExporting_2341_; 
v_isExporting_2341_ = lean_ctor_get_uint8(v_env_2339_, sizeof(void*)*8);
if (v_isExporting_2341_ == 0)
{
lean_object* v___x_2342_; 
lean_dec_ref(v_env_2339_);
lean_dec(v_declHint_2335_);
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v_msg_2334_);
return v___x_2342_;
}
else
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
lean_inc_ref(v_env_2339_);
v___x_2343_ = l_Lean_Environment_setExporting(v_env_2339_, v___x_2340_);
lean_inc(v_declHint_2335_);
lean_inc_ref(v___x_2343_);
v___x_2344_ = l_Lean_Environment_contains(v___x_2343_, v_declHint_2335_, v_isExporting_2341_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_dec_ref(v___x_2343_);
lean_dec_ref(v_env_2339_);
lean_dec(v_declHint_2335_);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v_msg_2334_);
return v___x_2345_;
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v_c_2351_; lean_object* v___x_2352_; 
v___x_2346_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2);
v___x_2347_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3);
v___x_2348_ = l_Lean_Options_empty;
v___x_2349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2343_);
lean_ctor_set(v___x_2349_, 1, v___x_2346_);
lean_ctor_set(v___x_2349_, 2, v___x_2347_);
lean_ctor_set(v___x_2349_, 3, v___x_2348_);
lean_inc(v_declHint_2335_);
v___x_2350_ = l_Lean_MessageData_ofConstName(v_declHint_2335_, v___x_2340_);
v_c_2351_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2351_, 0, v___x_2349_);
lean_ctor_set(v_c_2351_, 1, v___x_2350_);
v___x_2352_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2339_, v_declHint_2335_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec_ref(v_env_2339_);
lean_dec(v_declHint_2335_);
v___x_2353_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
lean_ctor_set(v___x_2354_, 1, v_c_2351_);
v___x_2355_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_2356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v___x_2357_ = l_Lean_MessageData_note(v___x_2356_);
v___x_2358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2358_, 0, v_msg_2334_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
else
{
lean_object* v_val_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2395_; 
v_val_2360_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2362_ = v___x_2352_;
v_isShared_2363_ = v_isSharedCheck_2395_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_val_2360_);
lean_dec(v___x_2352_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2395_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v_mod_2367_; uint8_t v___x_2368_; 
v___x_2364_ = lean_box(0);
v___x_2365_ = l_Lean_Environment_header(v_env_2339_);
lean_dec_ref(v_env_2339_);
v___x_2366_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2365_);
v_mod_2367_ = lean_array_get(v___x_2364_, v___x_2366_, v_val_2360_);
lean_dec(v_val_2360_);
lean_dec_ref(v___x_2366_);
v___x_2368_ = l_Lean_isPrivateName(v_declHint_2335_);
lean_dec(v_declHint_2335_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2369_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_2370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
lean_ctor_set(v___x_2370_, 1, v_c_2351_);
v___x_2371_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_2372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2370_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = l_Lean_MessageData_ofName(v_mod_2367_);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = l_Lean_MessageData_note(v___x_2376_);
v___x_2378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2378_, 0, v_msg_2334_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set_tag(v___x_2362_, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2378_);
v___x_2380_ = v___x_2362_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2382_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
lean_ctor_set(v___x_2383_, 1, v_c_2351_);
v___x_2384_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_2385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2383_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = l_Lean_MessageData_ofName(v_mod_2367_);
v___x_2387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v___x_2388_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_2389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2387_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = l_Lean_MessageData_note(v___x_2389_);
v___x_2391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2391_, 0, v_msg_2334_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set_tag(v___x_2362_, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2391_);
v___x_2393_ = v___x_2362_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2396_; 
lean_dec_ref(v_env_2339_);
lean_dec(v_declHint_2335_);
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v_msg_2334_);
return v___x_2396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2397_, lean_object* v_declHint_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_2397_, v_declHint_2398_, v___y_2399_);
lean_dec(v___y_2399_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(lean_object* v_msg_2402_, lean_object* v_declHint_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2417_; 
v___x_2407_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_2402_, v_declHint_2403_, v___y_2405_);
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2417_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2417_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2412_ = l_Lean_unknownIdentifierMessageTag;
v___x_2413_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
lean_ctor_set(v___x_2413_, 1, v_a_2408_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2413_);
v___x_2415_ = v___x_2410_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8___boxed(lean_object* v_msg_2418_, lean_object* v_declHint_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_2418_, v_declHint_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(lean_object* v_ref_2424_, lean_object* v_msg_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_toCold_2429_; lean_object* v_currRecDepth_2430_; lean_object* v_ref_2431_; uint8_t v_diag_2432_; uint8_t v_suppressElabErrors_2433_; lean_object* v_ref_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v_toCold_2429_ = lean_ctor_get(v___y_2426_, 0);
v_currRecDepth_2430_ = lean_ctor_get(v___y_2426_, 1);
v_ref_2431_ = lean_ctor_get(v___y_2426_, 2);
v_diag_2432_ = lean_ctor_get_uint8(v___y_2426_, sizeof(void*)*3);
v_suppressElabErrors_2433_ = lean_ctor_get_uint8(v___y_2426_, sizeof(void*)*3 + 1);
v_ref_2434_ = l_Lean_replaceRef(v_ref_2424_, v_ref_2431_);
lean_inc(v_currRecDepth_2430_);
lean_inc_ref(v_toCold_2429_);
v___x_2435_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2435_, 0, v_toCold_2429_);
lean_ctor_set(v___x_2435_, 1, v_currRecDepth_2430_);
lean_ctor_set(v___x_2435_, 2, v_ref_2434_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*3, v_diag_2432_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*3 + 1, v_suppressElabErrors_2433_);
v___x_2436_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_msg_2425_, v___x_2435_, v___y_2427_);
lean_dec_ref_known(v___x_2435_, 3);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2437_, lean_object* v_msg_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_2437_, v_msg_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v_ref_2437_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(lean_object* v_ref_2443_, lean_object* v_msg_2444_, lean_object* v_declHint_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v___x_2449_; lean_object* v_a_2450_; lean_object* v___x_2451_; 
v___x_2449_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_2444_, v_declHint_2445_, v___y_2446_, v___y_2447_);
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref(v___x_2449_);
v___x_2451_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_2443_, v_a_2450_, v___y_2446_, v___y_2447_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2452_, lean_object* v_msg_2453_, lean_object* v_declHint_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_2452_, v_msg_2453_, v_declHint_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v_ref_2452_);
return v_res_2458_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2461_ = l_Lean_stringToMessageData(v___x_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2462_, lean_object* v_constName_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v___x_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2467_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2468_ = 0;
lean_inc(v_constName_2463_);
v___x_2469_ = l_Lean_MessageData_ofConstName(v_constName_2463_, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2467_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__1, &l_Lean_Compiler_LCNF_nameToImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1);
v___x_2472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_2462_, v___x_2472_, v_constName_2463_, v___y_2464_, v___y_2465_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2474_, lean_object* v_constName_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(v_ref_2474_, v_constName_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v_ref_2474_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(lean_object* v_constName_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_ref_2484_; lean_object* v___x_2485_; 
v_ref_2484_ = lean_ctor_get(v___y_2481_, 2);
v___x_2485_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(v_ref_2484_, v_constName_2480_, v___y_2481_, v___y_2482_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(v_constName_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0(lean_object* v_constName_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; lean_object* v_env_2496_; uint8_t v___x_2497_; lean_object* v___x_2498_; 
v___x_2495_ = lean_st_ref_get(v___y_2493_);
v_env_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc_ref(v_env_2496_);
lean_dec(v___x_2495_);
v___x_2497_ = 0;
lean_inc(v_constName_2491_);
v___x_2498_ = l_Lean_Environment_find_x3f(v_env_2496_, v_constName_2491_, v___x_2497_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(v_constName_2491_, v___y_2492_, v___y_2493_);
return v___x_2499_;
}
else
{
lean_object* v_val_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_constName_2491_);
v_val_2500_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2498_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_val_2500_);
lean_dec(v___x_2498_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set_tag(v___x_2502_, 0);
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_val_2500_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0___boxed(lean_object* v_constName_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0(v_constName_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
return v_res_2512_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2514_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_2515_ = lean_unsigned_to_nat(49u);
v___x_2516_ = lean_unsigned_to_nat(303u);
v___x_2517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__0));
v___x_2518_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_2519_ = l_mkPanicMessageWithDecl(v___x_2518_, v___x_2517_, v___x_2516_, v___x_2515_, v___x_2514_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4(lean_object* v_as_2520_, size_t v_sz_2521_, size_t v_i_2522_, lean_object* v_b_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_a_2528_; uint8_t v___x_2532_; 
v___x_2532_ = lean_usize_dec_lt(v_i_2522_, v_sz_2521_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; 
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v_b_2523_);
return v___x_2533_;
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2535_; 
v_a_2534_ = lean_array_uget_borrowed(v_as_2520_, v_i_2522_);
lean_inc(v_a_2534_);
v___x_2535_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0(v_a_2534_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2537_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2535_, 1);
v___x_2537_ = lean_box(0);
if (lean_obj_tag(v_a_2536_) == 5)
{
lean_object* v_val_2538_; lean_object* v_ctors_2539_; lean_object* v___x_2540_; 
v_val_2538_ = lean_ctor_get(v_a_2536_, 0);
lean_inc_ref(v_val_2538_);
lean_dec_ref_known(v_a_2536_, 1);
v_ctors_2539_ = lean_ctor_get(v_val_2538_, 4);
lean_inc(v_ctors_2539_);
lean_dec_ref(v_val_2538_);
v___x_2540_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(v_ctors_2539_, v___x_2537_, v___y_2524_, v___y_2525_);
lean_dec(v_ctors_2539_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_dec_ref_known(v___x_2540_, 1);
v_a_2528_ = v___x_2537_;
goto v___jp_2527_;
}
else
{
return v___x_2540_;
}
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec(v_a_2536_);
v___x_2541_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1);
v___x_2542_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(v___x_2541_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_dec_ref_known(v___x_2542_, 1);
v_a_2528_ = v___x_2537_;
goto v___jp_2527_;
}
else
{
return v___x_2542_;
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
v_a_2543_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2535_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2535_);
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
v___jp_2527_:
{
size_t v___x_2529_; size_t v___x_2530_; 
v___x_2529_ = ((size_t)1ULL);
v___x_2530_ = lean_usize_add(v_i_2522_, v___x_2529_);
v_i_2522_ = v___x_2530_;
v_b_2523_ = v_a_2528_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___boxed(lean_object* v_as_2551_, lean_object* v_sz_2552_, lean_object* v_i_2553_, lean_object* v_b_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
size_t v_sz_boxed_2558_; size_t v_i_boxed_2559_; lean_object* v_res_2560_; 
v_sz_boxed_2558_ = lean_unbox_usize(v_sz_2552_);
lean_dec(v_sz_2552_);
v_i_boxed_2559_ = lean_unbox_usize(v_i_2553_);
lean_dec(v_i_2553_);
v_res_2560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4(v_as_2551_, v_sz_boxed_2558_, v_i_boxed_2559_, v_b_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec_ref(v_as_2551_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3(lean_object* v_as_2561_, size_t v_sz_2562_, size_t v_i_2563_, lean_object* v_b_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
uint8_t v___x_2568_; 
v___x_2568_ = lean_usize_dec_lt(v_i_2563_, v_sz_2562_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2569_, 0, v_b_2564_);
return v___x_2569_;
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2571_; 
v_a_2570_ = lean_array_uget_borrowed(v_as_2561_, v_i_2563_);
lean_inc(v_a_2570_);
v___x_2571_ = l_Lean_Compiler_LCNF_setOtherDeclMonoType(v_a_2570_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v___x_2572_; 
lean_dec_ref_known(v___x_2571_, 1);
lean_inc(v_a_2570_);
v___x_2572_ = l_Lean_Compiler_LCNF_setImpureType(v_a_2570_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v___x_2573_; size_t v___x_2574_; size_t v___x_2575_; 
lean_dec_ref_known(v___x_2572_, 1);
v___x_2573_ = lean_box(0);
v___x_2574_ = ((size_t)1ULL);
v___x_2575_ = lean_usize_add(v_i_2563_, v___x_2574_);
v_i_2563_ = v___x_2575_;
v_b_2564_ = v___x_2573_;
goto _start;
}
else
{
return v___x_2572_;
}
}
else
{
return v___x_2571_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3___boxed(lean_object* v_as_2577_, lean_object* v_sz_2578_, lean_object* v_i_2579_, lean_object* v_b_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
size_t v_sz_boxed_2584_; size_t v_i_boxed_2585_; lean_object* v_res_2586_; 
v_sz_boxed_2584_ = lean_unbox_usize(v_sz_2578_);
lean_dec(v_sz_2578_);
v_i_boxed_2585_ = lean_unbox_usize(v_i_2579_);
lean_dec(v_i_2579_);
v_res_2586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3(v_as_2577_, v_sz_boxed_2584_, v_i_boxed_2585_, v_b_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_as_2577_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(lean_object* v_as_2587_, size_t v_i_2588_, size_t v_stop_2589_, lean_object* v_b_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_a_2594_; uint8_t v___x_2598_; 
v___x_2598_ = lean_usize_dec_eq(v_i_2588_, v_stop_2589_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; lean_object* v_env_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2599_ = lean_st_ref_get(v___y_2591_);
v_env_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc_ref(v_env_2600_);
lean_dec(v___x_2599_);
v___x_2601_ = lean_array_uget_borrowed(v_as_2587_, v_i_2588_);
lean_inc(v___x_2601_);
v___x_2602_ = l_Lean_Environment_find_x3f(v_env_2600_, v___x_2601_, v___x_2598_);
if (lean_obj_tag(v___x_2602_) == 1)
{
lean_object* v_val_2603_; 
v_val_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_val_2603_);
lean_dec_ref_known(v___x_2602_, 1);
if (lean_obj_tag(v_val_2603_) == 5)
{
lean_object* v___x_2604_; 
lean_dec_ref_known(v_val_2603_, 1);
lean_inc(v___x_2601_);
v___x_2604_ = lean_array_push(v_b_2590_, v___x_2601_);
v_a_2594_ = v___x_2604_;
goto v___jp_2593_;
}
else
{
lean_dec(v_val_2603_);
v_a_2594_ = v_b_2590_;
goto v___jp_2593_;
}
}
else
{
lean_dec(v___x_2602_);
v_a_2594_ = v_b_2590_;
goto v___jp_2593_;
}
}
else
{
lean_object* v___x_2605_; 
v___x_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2605_, 0, v_b_2590_);
return v___x_2605_;
}
v___jp_2593_:
{
size_t v___x_2595_; size_t v___x_2596_; 
v___x_2595_ = ((size_t)1ULL);
v___x_2596_ = lean_usize_add(v_i_2588_, v___x_2595_);
v_i_2588_ = v___x_2596_;
v_b_2590_ = v_a_2594_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg___boxed(lean_object* v_as_2606_, lean_object* v_i_2607_, lean_object* v_stop_2608_, lean_object* v_b_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
size_t v_i_boxed_2612_; size_t v_stop_boxed_2613_; lean_object* v_res_2614_; 
v_i_boxed_2612_ = lean_unbox_usize(v_i_2607_);
lean_dec(v_i_2607_);
v_stop_boxed_2613_ = lean_unbox_usize(v_stop_2608_);
lean_dec(v_stop_2608_);
v_res_2614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_as_2606_, v_i_boxed_2612_, v_stop_boxed_2613_, v_b_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v_as_2606_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compileInductives(lean_object* v_typeNames_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_){
_start:
{
lean_object* v_a_2622_; lean_object* v___y_2638_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2648_ = lean_unsigned_to_nat(0u);
v___x_2649_ = lean_array_get_size(v_typeNames_2617_);
v___x_2650_ = ((lean_object*)(l_Lean_Compiler_LCNF_compileInductives___closed__0));
v___x_2651_ = lean_nat_dec_lt(v___x_2648_, v___x_2649_);
if (v___x_2651_ == 0)
{
v_a_2622_ = v___x_2650_;
goto v___jp_2621_;
}
else
{
uint8_t v___x_2652_; 
v___x_2652_ = lean_nat_dec_le(v___x_2649_, v___x_2649_);
if (v___x_2652_ == 0)
{
if (v___x_2651_ == 0)
{
v_a_2622_ = v___x_2650_;
goto v___jp_2621_;
}
else
{
size_t v___x_2653_; size_t v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = ((size_t)0ULL);
v___x_2654_ = lean_usize_of_nat(v___x_2649_);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_typeNames_2617_, v___x_2653_, v___x_2654_, v___x_2650_, v_a_2619_);
v___y_2638_ = v___x_2655_;
goto v___jp_2637_;
}
}
else
{
size_t v___x_2656_; size_t v___x_2657_; lean_object* v___x_2658_; 
v___x_2656_ = ((size_t)0ULL);
v___x_2657_ = lean_usize_of_nat(v___x_2649_);
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_typeNames_2617_, v___x_2656_, v___x_2657_, v___x_2650_, v_a_2619_);
v___y_2638_ = v___x_2658_;
goto v___jp_2637_;
}
}
v___jp_2621_:
{
lean_object* v___x_2623_; size_t v_sz_2624_; size_t v___x_2625_; lean_object* v___x_2626_; 
v___x_2623_ = lean_box(0);
v_sz_2624_ = lean_array_size(v_a_2622_);
v___x_2625_ = ((size_t)0ULL);
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(v_a_2622_, v_sz_2624_, v___x_2625_, v___x_2623_, v_a_2618_, v_a_2619_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v___x_2627_; 
lean_dec_ref_known(v___x_2626_, 1);
v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3(v_a_2622_, v_sz_2624_, v___x_2625_, v___x_2623_, v_a_2618_, v_a_2619_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v___x_2628_; 
lean_dec_ref_known(v___x_2627_, 1);
v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4(v_a_2622_, v_sz_2624_, v___x_2625_, v___x_2623_, v_a_2618_, v_a_2619_);
lean_dec_ref(v_a_2622_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2635_ == 0)
{
lean_object* v_unused_2636_; 
v_unused_2636_ = lean_ctor_get(v___x_2628_, 0);
lean_dec(v_unused_2636_);
v___x_2630_ = v___x_2628_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_dec(v___x_2628_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2623_);
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2623_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
else
{
return v___x_2628_;
}
}
else
{
lean_dec_ref(v_a_2622_);
return v___x_2627_;
}
}
else
{
lean_dec_ref(v_a_2622_);
return v___x_2626_;
}
}
v___jp_2637_:
{
if (lean_obj_tag(v___y_2638_) == 0)
{
lean_object* v_a_2639_; 
v_a_2639_ = lean_ctor_get(v___y_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___y_2638_, 1);
v_a_2622_ = v_a_2639_;
goto v___jp_2621_;
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
v_a_2640_ = lean_ctor_get(v___y_2638_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___y_2638_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___y_2638_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___y_2638_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compileInductives___boxed(lean_object* v_typeNames_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_Compiler_LCNF_compileInductives(v_typeNames_2659_, v_a_2660_, v_a_2661_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec_ref(v_typeNames_2659_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1(lean_object* v_as_2664_, lean_object* v_as_x27_2665_, lean_object* v_b_2666_, lean_object* v_a_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(v_as_x27_2665_, v_b_2666_, v___y_2668_, v___y_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___boxed(lean_object* v_as_2672_, lean_object* v_as_x27_2673_, lean_object* v_b_2674_, lean_object* v_a_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1(v_as_2672_, v_as_x27_2673_, v_b_2674_, v_a_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v_as_x27_2673_);
lean_dec(v_as_2672_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5(lean_object* v_as_2680_, size_t v_i_2681_, size_t v_stop_2682_, lean_object* v_b_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_as_2680_, v_i_2681_, v_stop_2682_, v_b_2683_, v___y_2685_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___boxed(lean_object* v_as_2688_, lean_object* v_i_2689_, lean_object* v_stop_2690_, lean_object* v_b_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
size_t v_i_boxed_2695_; size_t v_stop_boxed_2696_; lean_object* v_res_2697_; 
v_i_boxed_2695_ = lean_unbox_usize(v_i_2689_);
lean_dec(v_i_2689_);
v_stop_boxed_2696_ = lean_unbox_usize(v_stop_2690_);
lean_dec(v_stop_2690_);
v_res_2697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5(v_as_2688_, v_i_boxed_2695_, v_stop_boxed_2696_, v_b_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec_ref(v_as_2688_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0(lean_object* v_00_u03b1_2698_, lean_object* v_constName_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(v_constName_2699_, v___y_2700_, v___y_2701_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2704_, lean_object* v_constName_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0(v_00_u03b1_2704_, v_constName_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2710_, lean_object* v_ref_2711_, lean_object* v_constName_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(v_ref_2711_, v_constName_2712_, v___y_2713_, v___y_2714_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2717_, lean_object* v_ref_2718_, lean_object* v_constName_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1(v_00_u03b1_2717_, v_ref_2718_, v_constName_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v_ref_2718_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b1_2724_, lean_object* v_ref_2725_, lean_object* v_msg_2726_, lean_object* v_declHint_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_2725_, v_msg_2726_, v_declHint_2727_, v___y_2728_, v___y_2729_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___boxed(lean_object* v_00_u03b1_2732_, lean_object* v_ref_2733_, lean_object* v_msg_2734_, lean_object* v_declHint_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7(v_00_u03b1_2732_, v_ref_2733_, v_msg_2734_, v_declHint_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v_ref_2733_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(lean_object* v_msg_2740_, lean_object* v_declHint_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_2740_, v_declHint_2741_, v___y_2743_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2746_, lean_object* v_declHint_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(v_msg_2746_, v_declHint_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_2752_, lean_object* v_ref_2753_, lean_object* v_msg_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_2753_, v_msg_2754_, v___y_2755_, v___y_2756_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2759_, lean_object* v_ref_2760_, lean_object* v_msg_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9(v_00_u03b1_2759_, v_ref_2760_, v_msg_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v_ref_2760_);
return v_res_2765_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Irrelevant(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt);
lean_dec_ref(res);
l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo_default = _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo_default);
l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo = _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo);
l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default = _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default);
l_Lean_Compiler_LCNF_instInhabitedCtorLayout = _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCtorLayout);
res = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Irrelevant(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
}
#ifdef __cplusplus
}
#endif
