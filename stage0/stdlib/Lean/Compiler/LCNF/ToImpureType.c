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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_312_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_312_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_312_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_312_;
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
lean_object* v___x_262_; 
lean_dec_ref(v_struct_252_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_262_ = v___x_247_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_242_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
else
{
if (lean_obj_tag(v_struct_252_) == 5)
{
lean_object* v_fn_264_; 
v_fn_264_ = lean_ctor_get(v_struct_252_, 0);
lean_inc_ref(v_fn_264_);
lean_dec_ref_known(v_struct_252_, 2);
if (lean_obj_tag(v_fn_264_) == 4)
{
lean_object* v_declName_265_; 
v_declName_265_ = lean_ctor_get(v_fn_264_, 0);
lean_inc(v_declName_265_);
if (lean_obj_tag(v_declName_265_) == 1)
{
lean_object* v_pre_266_; 
v_pre_266_ = lean_ctor_get(v_declName_265_, 0);
lean_inc(v_pre_266_);
if (lean_obj_tag(v_pre_266_) == 1)
{
lean_object* v_pre_267_; 
v_pre_267_ = lean_ctor_get(v_pre_266_, 0);
if (lean_obj_tag(v_pre_267_) == 0)
{
lean_object* v_us_268_; lean_object* v_str_269_; lean_object* v_str_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_us_268_ = lean_ctor_get(v_fn_264_, 1);
lean_inc(v_us_268_);
lean_dec_ref_known(v_fn_264_, 2);
v_str_269_ = lean_ctor_get(v_declName_265_, 1);
lean_inc_ref(v_str_269_);
lean_dec_ref_known(v_declName_265_, 2);
v_str_270_ = lean_ctor_get(v_pre_266_, 1);
lean_inc_ref(v_str_270_);
lean_dec_ref_known(v_pre_266_, 2);
v___x_271_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__1));
v___x_272_ = lean_string_dec_eq(v_str_270_, v___x_271_);
lean_dec_ref(v_str_270_);
if (v___x_272_ == 0)
{
lean_object* v___x_274_; 
lean_dec_ref(v_str_269_);
lean_dec(v_us_268_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_274_ = v___x_247_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_242_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
else
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__2));
v___x_277_ = lean_string_dec_eq(v_str_269_, v___x_276_);
lean_dec_ref(v_str_269_);
if (v___x_277_ == 0)
{
lean_object* v___x_279_; 
lean_dec(v_us_268_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_279_ = v___x_247_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_242_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
else
{
if (lean_obj_tag(v_us_268_) == 0)
{
lean_object* v___x_281_; lean_object* v___x_283_; 
lean_dec(v_a_242_);
v___x_281_ = lean_box(v___x_277_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_281_);
v___x_283_ = v___x_247_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
else
{
lean_object* v___x_286_; 
lean_dec(v_us_268_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_286_ = v___x_247_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_242_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
else
{
lean_object* v___x_289_; 
lean_dec_ref_known(v_pre_266_, 2);
lean_dec_ref_known(v_declName_265_, 2);
lean_dec_ref_known(v_fn_264_, 2);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_289_ = v___x_247_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_242_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
else
{
lean_object* v___x_292_; 
lean_dec(v_pre_266_);
lean_dec_ref_known(v_declName_265_, 2);
lean_dec_ref_known(v_fn_264_, 2);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_292_ = v___x_247_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_242_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
lean_object* v___x_295_; 
lean_dec_ref_known(v_fn_264_, 2);
lean_dec(v_declName_265_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_295_ = v___x_247_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_242_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
else
{
lean_object* v___x_298_; 
lean_dec_ref(v_fn_264_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_298_ = v___x_247_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_242_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
else
{
lean_object* v___x_301_; 
lean_dec_ref(v_struct_252_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_301_ = v___x_247_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_242_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
else
{
lean_object* v___x_304_; 
lean_dec_ref_known(v_typeName_249_, 2);
lean_dec_ref_known(v_a_245_, 3);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_304_ = v___x_247_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_242_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
else
{
lean_object* v___x_307_; 
lean_dec(v_typeName_249_);
lean_dec_ref_known(v_a_245_, 3);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_307_ = v___x_247_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_242_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_object* v___x_310_; 
lean_dec(v_a_245_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_242_);
v___x_310_ = v___x_247_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_242_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec(v_a_242_);
v_a_313_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_244_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_244_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___boxed(lean_object* v_type_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType(v_type_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f(lean_object* v_declName_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt;
v___x_334_ = ((lean_object*)(l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f___closed__0));
v___x_335_ = l_Lean_Compiler_LCNF_Irrelevant_setHasTrivialStructure_x3f(v___x_333_, v___x_334_, v_declName_329_, v_a_330_, v_a_331_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f___boxed(lean_object* v_declName_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f(v_declName_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(lean_object* v_declName_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt;
v___x_346_ = l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(v___x_345_, v_declName_341_, v_a_342_, v_a_343_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___boxed(lean_object* v_declName_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_declName_347_, v_a_348_, v_a_349_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
return v_res_351_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_box(0);
v___x_362_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__7));
v___x_363_ = l_Lean_Expr_const___override(v___x_362_, v___x_361_);
return v___x_363_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8);
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_box(0);
v___x_370_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__11));
v___x_371_ = l_Lean_Expr_const___override(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_box(0);
v___x_377_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__14));
v___x_378_ = l_Lean_Expr_const___override(v___x_377_, v___x_376_);
return v___x_378_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = lean_box(0);
v___x_384_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__17));
v___x_385_ = l_Lean_Expr_const___override(v___x_384_, v___x_383_);
return v___x_385_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18);
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_box(0);
v___x_391_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__20));
v___x_392_ = l_Lean_Expr_const___override(v___x_391_, v___x_390_);
return v___x_392_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21);
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = lean_box(0);
v___x_398_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__23));
v___x_399_ = l_Lean_Expr_const___override(v___x_398_, v___x_397_);
return v___x_399_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24);
v___x_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
return v___x_401_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_box(0);
v___x_405_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__26));
v___x_406_ = l_Lean_Expr_const___override(v___x_405_, v___x_404_);
return v___x_406_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5);
v___x_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8);
v___x_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11);
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(lean_object* v_x_415_){
_start:
{
if (lean_obj_tag(v_x_415_) == 1)
{
lean_object* v_pre_416_; 
v_pre_416_ = lean_ctor_get(v_x_415_, 0);
if (lean_obj_tag(v_pre_416_) == 0)
{
lean_object* v_str_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_str_417_ = lean_ctor_get(v_x_415_, 1);
v___x_418_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9));
v___x_419_ = lean_string_dec_eq(v_str_417_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6));
v___x_421_ = lean_string_dec_eq(v_str_417_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3));
v___x_423_ = lean_string_dec_eq(v_str_417_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__0));
v___x_425_ = lean_string_dec_eq(v_str_417_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__1));
v___x_427_ = lean_string_dec_eq(v_str_417_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__2));
v___x_429_ = lean_string_dec_eq(v_str_417_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__3));
v___x_431_ = lean_string_dec_eq(v_str_417_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__4));
v___x_433_ = lean_string_dec_eq(v_str_417_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__5));
v___x_435_ = lean_string_dec_eq(v_str_417_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__6));
v___x_437_ = lean_string_dec_eq(v_str_417_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
v___x_438_ = lean_box(0);
return v___x_438_;
}
else
{
lean_object* v___x_439_; 
v___x_439_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9);
return v___x_439_;
}
}
else
{
lean_object* v___x_440_; 
v___x_440_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13);
return v___x_440_;
}
}
else
{
lean_object* v___x_441_; 
v___x_441_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16);
return v___x_441_;
}
}
else
{
lean_object* v___x_442_; 
v___x_442_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19);
return v___x_442_;
}
}
else
{
lean_object* v___x_443_; 
v___x_443_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22);
return v___x_443_;
}
}
else
{
lean_object* v___x_444_; 
v___x_444_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25);
return v___x_444_;
}
}
else
{
lean_object* v___x_445_; 
v___x_445_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28);
return v___x_445_;
}
}
else
{
lean_object* v___x_446_; 
v___x_446_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29);
return v___x_446_;
}
}
else
{
lean_object* v___x_447_; 
v___x_447_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30);
return v___x_447_;
}
}
else
{
lean_object* v___x_448_; 
v___x_448_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31);
return v___x_448_;
}
}
else
{
lean_object* v___x_449_; 
v___x_449_ = lean_box(0);
return v___x_449_;
}
}
else
{
lean_object* v___x_450_; 
v___x_450_ = lean_box(0);
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___boxed(lean_object* v_x_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(v_x_451_);
lean_dec(v_x_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(lean_object* v_msg_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___f_458_; lean_object* v___x_5765__overap_459_; lean_object* v___x_460_; 
v___f_458_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0));
v___x_5765__overap_459_ = lean_panic_fn_borrowed(v___f_458_, v_msg_454_);
lean_inc(v___y_456_);
lean_inc_ref(v___y_455_);
v___x_460_ = lean_apply_3(v___x_5765__overap_459_, v___y_455_, v___y_456_, lean_box(0));
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___boxed(lean_object* v_msg_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(v_msg_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0(lean_object* v_k_466_, lean_object* v_b_467_, lean_object* v_c_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; 
lean_inc(v___y_472_);
lean_inc_ref(v___y_471_);
lean_inc(v___y_470_);
lean_inc_ref(v___y_469_);
v___x_474_ = lean_apply_7(v_k_466_, v_b_467_, v_c_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, lean_box(0));
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0___boxed(lean_object* v_k_475_, lean_object* v_b_476_, lean_object* v_c_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0(v_k_475_, v_b_476_, v_c_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg(lean_object* v_type_484_, lean_object* v_k_485_, uint8_t v_cleanupAnnotations_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v___f_492_; uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___f_492_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_492_, 0, v_k_485_);
v___x_493_ = 0;
v___x_494_ = lean_box(0);
v___x_495_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_493_, v___x_494_, v_type_484_, v___f_492_, v_cleanupAnnotations_486_, v___x_493_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
v_a_504_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_495_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_495_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___boxed(lean_object* v_type_512_, lean_object* v_k_513_, lean_object* v_cleanupAnnotations_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_520_; lean_object* v_res_521_; 
v_cleanupAnnotations_boxed_520_ = lean_unbox(v_cleanupAnnotations_514_);
v_res_521_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg(v_type_512_, v_k_513_, v_cleanupAnnotations_boxed_520_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2(lean_object* v_00_u03b1_522_, lean_object* v_type_523_, lean_object* v_k_524_, uint8_t v_cleanupAnnotations_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg(v_type_523_, v_k_524_, v_cleanupAnnotations_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___boxed(lean_object* v_00_u03b1_532_, lean_object* v_type_533_, lean_object* v_k_534_, lean_object* v_cleanupAnnotations_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_541_; lean_object* v_res_542_; 
v_cleanupAnnotations_boxed_541_ = lean_unbox(v_cleanupAnnotations_535_);
v_res_542_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2(v_00_u03b1_532_, v_type_533_, v_k_534_, v_cleanupAnnotations_boxed_541_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(lean_object* v_a_546_, lean_object* v_b_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_array_553_; lean_object* v_start_554_; lean_object* v_stop_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_613_; 
v_array_553_ = lean_ctor_get(v_a_546_, 0);
v_start_554_ = lean_ctor_get(v_a_546_, 1);
v_stop_555_ = lean_ctor_get(v_a_546_, 2);
v_isSharedCheck_613_ = !lean_is_exclusive(v_a_546_);
if (v_isSharedCheck_613_ == 0)
{
v___x_557_ = v_a_546_;
v_isShared_558_ = v_isSharedCheck_613_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_stop_555_);
lean_inc(v_start_554_);
lean_inc(v_array_553_);
lean_dec(v_a_546_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_613_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
uint8_t v___x_559_; 
v___x_559_ = lean_nat_dec_lt(v_start_554_, v_stop_555_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
lean_del_object(v___x_557_);
lean_dec(v_stop_555_);
lean_dec(v_start_554_);
lean_dec_ref(v_array_553_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v_b_547_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec_ref(v_b_547_);
v___x_561_ = lean_array_fget_borrowed(v_array_553_, v_start_554_);
v___x_562_ = l_Lean_Expr_fvarId_x21(v___x_561_);
v___x_563_ = l_Lean_FVarId_getType___redArg(v___x_562_, v___y_548_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_565_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_563_, 1);
v___x_565_ = l_Lean_Compiler_LCNF_toLCNFType(v_a_564_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_565_, 1);
v___x_567_ = l_Lean_Compiler_LCNF_toMonoType(v_a_566_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_588_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_588_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_588_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_588_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; uint8_t v___x_573_; uint8_t v___x_574_; 
v___x_572_ = lean_box(0);
v___x_573_ = l_Lean_Expr_isErased(v_a_568_);
lean_dec(v_a_568_);
v___x_574_ = lean_bool_not(v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
lean_del_object(v___x_570_);
v___x_575_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___closed__0));
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_add(v_start_554_, v___x_576_);
lean_dec(v_start_554_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v___x_577_);
v___x_579_ = v___x_557_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_array_553_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_stop_555_);
v___x_579_ = v_reuseFailAlloc_581_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
v_a_546_ = v___x_579_;
v_b_547_ = v___x_575_;
goto _start;
}
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
lean_del_object(v___x_557_);
lean_dec(v_stop_555_);
lean_dec(v_start_554_);
lean_dec_ref(v_array_553_);
v___x_582_ = lean_box(v___x_574_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v___x_572_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_584_);
v___x_586_ = v___x_570_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_del_object(v___x_557_);
lean_dec(v_stop_555_);
lean_dec(v_start_554_);
lean_dec_ref(v_array_553_);
v_a_589_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_567_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_567_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_del_object(v___x_557_);
lean_dec(v_stop_555_);
lean_dec(v_start_554_);
lean_dec_ref(v_array_553_);
v_a_597_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_565_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_565_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_del_object(v___x_557_);
lean_dec(v_stop_555_);
lean_dec(v_start_554_);
lean_dec_ref(v_array_553_);
v_a_605_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_563_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_563_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___boxed(lean_object* v_a_614_, lean_object* v_b_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(v_a_614_, v_b_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0(uint8_t v___x_622_, lean_object* v_numParams_623_, lean_object* v___x_624_, lean_object* v_params_625_, lean_object* v_x_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_lower_633_; lean_object* v_upper_634_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = lean_array_get_size(v_params_625_);
v___x_661_ = lean_nat_dec_le(v_numParams_623_, v___x_624_);
if (v___x_661_ == 0)
{
lean_dec(v___x_624_);
v_lower_633_ = v_numParams_623_;
v_upper_634_ = v___x_660_;
goto v___jp_632_;
}
else
{
lean_dec(v_numParams_623_);
v_lower_633_ = v___x_624_;
v_upper_634_ = v___x_660_;
goto v___jp_632_;
}
v___jp_632_:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = l_Array_toSubarray___redArg(v_params_625_, v_lower_633_, v_upper_634_);
v___x_636_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___closed__0));
v___x_637_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(v___x_635_, v___x_636_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_651_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_651_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_651_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_651_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_fst_642_; 
v_fst_642_ = lean_ctor_get(v_a_638_, 0);
lean_inc(v_fst_642_);
lean_dec(v_a_638_);
if (lean_obj_tag(v_fst_642_) == 0)
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = lean_box(v___x_622_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_643_);
v___x_645_ = v___x_640_;
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
else
{
lean_object* v_val_647_; lean_object* v___x_649_; 
v_val_647_ = lean_ctor_get(v_fst_642_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v_fst_642_, 1);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v_val_647_);
v___x_649_ = v___x_640_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_val_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
v_a_652_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_637_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_637_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0___boxed(lean_object* v___x_662_, lean_object* v_numParams_663_, lean_object* v___x_664_, lean_object* v_params_665_, lean_object* v_x_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
uint8_t v___x_7125__boxed_672_; lean_object* v_res_673_; 
v___x_7125__boxed_672_ = lean_unbox(v___x_662_);
v_res_673_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0(v___x_7125__boxed_672_, v_numParams_663_, v___x_664_, v_params_665_, v_x_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v_x_666_);
return v_res_673_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_677_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_678_ = lean_unsigned_to_nat(58u);
v___x_679_ = lean_unsigned_to_nat(92u);
v___x_680_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__1));
v___x_681_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_682_ = l_mkPanicMessageWithDecl(v___x_681_, v___x_680_, v___x_679_, v___x_678_, v___x_677_);
return v___x_682_;
}
}
static uint64_t _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_689_; uint64_t v___x_690_; 
v___x_689_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__4));
v___x_690_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_689_);
return v___x_690_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__6(void){
_start:
{
uint64_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_691_ = lean_uint64_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__5);
v___x_692_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__4));
v___x_693_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set_uint64(v___x_693_, sizeof(void*)*1, v___x_691_);
return v___x_693_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_694_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = lean_unsigned_to_nat(32u);
v___x_698_ = lean_mk_empty_array_with_capacity(v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10(void){
_start:
{
size_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_700_ = ((size_t)5ULL);
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_unsigned_to_nat(32u);
v___x_703_ = lean_mk_empty_array_with_capacity(v___x_702_);
v___x_704_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__9);
v___x_705_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v___x_703_);
lean_ctor_set(v___x_705_, 2, v___x_701_);
lean_ctor_set(v___x_705_, 3, v___x_701_);
lean_ctor_set_usize(v___x_705_, 4, v___x_700_);
return v___x_705_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__11(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_706_ = lean_box(1);
v___x_707_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10);
v___x_708_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8);
v___x_709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___x_707_);
lean_ctor_set(v___x_709_, 2, v___x_706_);
return v___x_709_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13(void){
_start:
{
uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_712_ = 1;
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = lean_box(0);
v___x_715_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__12));
v___x_716_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__11);
v___x_717_ = lean_box(1);
v___x_718_ = 0;
v___x_719_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__6);
v___x_720_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___x_717_);
lean_ctor_set(v___x_720_, 2, v___x_716_);
lean_ctor_set(v___x_720_, 3, v___x_715_);
lean_ctor_set(v___x_720_, 4, v___x_714_);
lean_ctor_set(v___x_720_, 5, v___x_713_);
lean_ctor_set(v___x_720_, 6, v___x_714_);
lean_ctor_set_uint8(v___x_720_, sizeof(void*)*7, v___x_718_);
lean_ctor_set_uint8(v___x_720_, sizeof(void*)*7 + 1, v___x_718_);
lean_ctor_set_uint8(v___x_720_, sizeof(void*)*7 + 2, v___x_718_);
lean_ctor_set_uint8(v___x_720_, sizeof(void*)*7 + 3, v___x_712_);
return v___x_720_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__14(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
lean_ctor_set(v___x_723_, 2, v___x_722_);
lean_ctor_set(v___x_723_, 3, v___x_722_);
lean_ctor_set(v___x_723_, 4, v___x_721_);
lean_ctor_set(v___x_723_, 5, v___x_721_);
lean_ctor_set(v___x_723_, 6, v___x_721_);
lean_ctor_set(v___x_723_, 7, v___x_721_);
lean_ctor_set(v___x_723_, 8, v___x_721_);
lean_ctor_set(v___x_723_, 9, v___x_721_);
return v___x_723_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__15(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8);
v___x_725_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
lean_ctor_set(v___x_725_, 2, v___x_724_);
lean_ctor_set(v___x_725_, 3, v___x_724_);
lean_ctor_set(v___x_725_, 4, v___x_724_);
lean_ctor_set(v___x_725_, 5, v___x_724_);
return v___x_725_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__16(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8);
v___x_727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
lean_ctor_set(v___x_727_, 2, v___x_726_);
lean_ctor_set(v___x_727_, 3, v___x_726_);
lean_ctor_set(v___x_727_, 4, v___x_726_);
return v___x_727_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_728_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__16, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__16_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__16);
v___x_729_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10);
v___x_730_ = lean_box(1);
v___x_731_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__15, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__15_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__15);
v___x_732_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__14);
v___x_733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_731_);
lean_ctor_set(v___x_733_, 2, v___x_730_);
lean_ctor_set(v___x_733_, 3, v___x_729_);
lean_ctor_set(v___x_733_, 4, v___x_728_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(lean_object* v___x_734_, lean_object* v_as_x27_735_, lean_object* v_b_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
if (lean_obj_tag(v_as_x27_735_) == 0)
{
lean_object* v___x_740_; 
lean_dec_ref(v___x_734_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v_b_736_);
return v___x_740_;
}
else
{
lean_object* v_head_741_; lean_object* v_tail_742_; uint8_t v_a_744_; lean_object* v___y_751_; lean_object* v___y_752_; uint8_t v___x_764_; lean_object* v___x_765_; 
v_head_741_ = lean_ctor_get(v_as_x27_735_, 0);
v_tail_742_ = lean_ctor_get(v_as_x27_735_, 1);
v___x_764_ = 0;
lean_inc(v_head_741_);
lean_inc_ref(v___x_734_);
v___x_765_ = l_Lean_Environment_find_x3f(v___x_734_, v_head_741_, v___x_764_);
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
v___x_777_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg(v_type_774_, v___f_776_, v___x_764_, v___x_769_, v___x_771_, v___y_737_, v___y_738_);
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
v_a_744_ = v___x_780_;
goto v___jp_743_;
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
v_a_744_ = v___x_782_;
goto v___jp_743_;
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_b_736_);
lean_dec_ref(v___x_734_);
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
v___y_751_ = v___y_737_;
v___y_752_ = v___y_738_;
goto v___jp_750_;
}
}
else
{
lean_dec(v___x_765_);
v___y_751_ = v___y_737_;
v___y_752_ = v___y_738_;
goto v___jp_750_;
}
v___jp_743_:
{
uint8_t v___x_745_; 
v___x_745_ = lean_bool_not(v_a_744_);
if (v___x_745_ == 0)
{
v_as_x27_735_ = v_tail_742_;
goto _start;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_unsigned_to_nat(1u);
v___x_748_ = lean_nat_add(v_b_736_, v___x_747_);
lean_dec(v_b_736_);
v_as_x27_735_ = v_tail_742_;
v_b_736_ = v___x_748_;
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
v_as_x27_735_ = v_tail_742_;
goto _start;
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_b_736_);
lean_dec_ref(v___x_734_);
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
v___x_941_ = lean_st_ref_set(v_a_909_, v___x_940_);
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
v___x_986_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___x_995_; lean_object* v_env_996_; lean_object* v_options_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_995_ = lean_st_ref_get(v___y_993_);
v_env_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc_ref(v_env_996_);
lean_dec(v___x_995_);
v_options_997_ = lean_ctor_get(v___y_992_, 2);
v___x_998_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2);
v___x_999_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3);
lean_inc_ref(v_options_997_);
v___x_1000_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1000_, 0, v_env_996_);
lean_ctor_set(v___x_1000_, 1, v___x_998_);
lean_ctor_set(v___x_1000_, 2, v___x_999_);
lean_ctor_set(v___x_1000_, 3, v_options_997_);
v___x_1001_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v_msgData_991_);
v___x_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___boxed(lean_object* v_msgData_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0(v_msgData_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(lean_object* v_msg_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_ref_1012_; lean_object* v___x_1013_; lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
v_ref_1012_ = lean_ctor_get(v___y_1009_, 5);
v___x_1013_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0(v_msg_1008_, v___y_1009_, v___y_1010_);
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
lean_inc(v_ref_1012_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v_ref_1012_);
lean_ctor_set(v___x_1018_, 1, v_a_1014_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 1);
lean_ctor_set(v___x_1016_, 0, v___x_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___boxed(lean_object* v_msg_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_msg_1023_, v___y_1024_, v___y_1025_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
return v_res_1027_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_Lean_Compiler_LCNF_nameToImpureType___closed__0));
v___x_1030_ = l_Lean_stringToMessageData(v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__3(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Lean_Compiler_LCNF_nameToImpureType___closed__2));
v___x_1033_ = l_Lean_stringToMessageData(v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_nameToImpureType(lean_object* v_name_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(v_name_1034_);
if (lean_obj_tag(v___x_1041_) == 1)
{
lean_object* v_val_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_name_1034_);
v_val_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_val_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set_tag(v___x_1044_, 0);
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_val_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
else
{
lean_object* v___x_1050_; lean_object* v_env_1051_; uint8_t v___x_1052_; lean_object* v___x_1053_; 
lean_dec(v___x_1041_);
v___x_1050_ = lean_st_ref_get(v_a_1036_);
v_env_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc_ref(v_env_1051_);
lean_dec(v___x_1050_);
v___x_1052_ = 0;
lean_inc(v_name_1034_);
v___x_1053_ = l_Lean_Environment_find_x3f(v_env_1051_, v_name_1034_, v___x_1052_);
if (lean_obj_tag(v___x_1053_) == 1)
{
lean_object* v_val_1054_; 
v_val_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_val_1054_);
lean_dec_ref_known(v___x_1053_, 1);
if (lean_obj_tag(v_val_1054_) == 5)
{
lean_object* v___x_1055_; lean_object* v_env_1056_; lean_object* v___x_1057_; lean_object* v_toEnvExtension_1058_; lean_object* v_asyncMode_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; 
lean_dec_ref_known(v_val_1054_, 1);
v___x_1055_ = lean_st_ref_get(v_a_1036_);
v_env_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc_ref(v_env_1056_);
lean_dec(v___x_1055_);
v___x_1057_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt;
v_toEnvExtension_1058_ = lean_ctor_get(v___x_1057_, 0);
v_asyncMode_1059_ = lean_ctor_get(v_toEnvExtension_1058_, 2);
v___x_1060_ = l_Lean_instInhabitedExpr;
v___x_1061_ = 0;
lean_inc(v_name_1034_);
v___x_1062_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1060_, v___x_1057_, v_env_1056_, v_name_1034_, v_asyncMode_1059_, v___x_1061_);
if (lean_obj_tag(v___x_1062_) == 1)
{
lean_object* v_val_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v_name_1034_);
v_val_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_val_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 0);
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_val_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec(v___x_1062_);
v___x_1071_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__1, &l_Lean_Compiler_LCNF_nameToImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1);
v___x_1072_ = l_Lean_MessageData_ofName(v_name_1034_);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__3, &l_Lean_Compiler_LCNF_nameToImpureType___closed__3_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__3);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v___x_1075_, v_a_1035_, v_a_1036_);
return v___x_1076_;
}
}
else
{
lean_dec(v_val_1054_);
lean_dec(v_name_1034_);
goto v___jp_1038_;
}
}
else
{
lean_dec(v___x_1053_);
lean_dec(v_name_1034_);
goto v___jp_1038_;
}
}
v___jp_1038_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_nameToImpureType___boxed(lean_object* v_name_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Compiler_LCNF_nameToImpureType(v_name_1077_, v_a_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0(lean_object* v_00_u03b1_1082_, lean_object* v_msg_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_msg_1083_, v___y_1084_, v___y_1085_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___boxed(lean_object* v_00_u03b1_1088_, lean_object* v_msg_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0(v_00_u03b1_1088_, v_msg_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
return v_res_1093_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(lean_object* v_type_1095_){
_start:
{
switch(lean_obj_tag(v_type_1095_))
{
case 4:
{
lean_object* v_declName_1096_; 
v_declName_1096_ = lean_ctor_get(v_type_1095_, 0);
if (lean_obj_tag(v_declName_1096_) == 1)
{
lean_object* v_pre_1097_; 
v_pre_1097_ = lean_ctor_get(v_declName_1096_, 0);
if (lean_obj_tag(v_pre_1097_) == 0)
{
lean_object* v_str_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v_str_1098_ = lean_ctor_get(v_declName_1096_, 1);
v___x_1099_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___closed__0));
v___x_1100_ = lean_string_dec_eq(v_str_1098_, v___x_1099_);
return v___x_1100_;
}
else
{
uint8_t v___x_1101_; 
v___x_1101_ = 0;
return v___x_1101_;
}
}
else
{
uint8_t v___x_1102_; 
v___x_1102_ = 0;
return v___x_1102_;
}
}
case 7:
{
lean_object* v_body_1103_; 
v_body_1103_ = lean_ctor_get(v_type_1095_, 2);
v_type_1095_ = v_body_1103_;
goto _start;
}
default: 
{
uint8_t v___x_1105_; 
v___x_1105_ = 0;
return v___x_1105_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___boxed(lean_object* v_type_1106_){
_start:
{
uint8_t v_res_1107_; lean_object* v_r_1108_; 
v_res_1107_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(v_type_1106_);
lean_dec_ref(v_type_1106_);
v_r_1108_ = lean_box(v_res_1107_);
return v_r_1108_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(lean_object* v_msg_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___f_1113_; lean_object* v___x_938__overap_1114_; lean_object* v___x_1115_; 
v___f_1113_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0));
v___x_938__overap_1114_ = lean_panic_fn_borrowed(v___f_1113_, v_msg_1109_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1110_);
v___x_1115_ = lean_apply_3(v___x_938__overap_1114_, v___y_1110_, v___y_1111_, lean_box(0));
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1___boxed(lean_object* v_msg_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(v_msg_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
return v_res_1120_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toImpureType___closed__1(void){
_start:
{
lean_object* v___x_1123_; lean_object* v_dummy_1124_; 
v___x_1123_ = lean_box(0);
v_dummy_1124_ = l_Lean_Expr_sort___override(v___x_1123_);
return v_dummy_1124_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toImpureType___closed__3(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1126_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_1127_ = lean_unsigned_to_nat(41u);
v___x_1128_ = lean_unsigned_to_nat(138u);
v___x_1129_ = ((lean_object*)(l_Lean_Compiler_LCNF_toImpureType___closed__2));
v___x_1130_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_1131_ = l_mkPanicMessageWithDecl(v___x_1130_, v___x_1129_, v___x_1128_, v___x_1127_, v___x_1126_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toImpureType___closed__4(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1132_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_1133_ = lean_unsigned_to_nat(9u);
v___x_1134_ = lean_unsigned_to_nat(150u);
v___x_1135_ = ((lean_object*)(l_Lean_Compiler_LCNF_toImpureType___closed__2));
v___x_1136_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_1137_ = l_mkPanicMessageWithDecl(v___x_1136_, v___x_1135_, v___x_1134_, v___x_1133_, v___x_1132_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpureType(lean_object* v_type_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
switch(lean_obj_tag(v_type_1138_))
{
case 4:
{
lean_object* v_declName_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_declName_1142_ = lean_ctor_get(v_type_1138_, 0);
lean_inc(v_declName_1142_);
lean_dec_ref_known(v_type_1138_, 2);
v___x_1143_ = ((lean_object*)(l_Lean_Compiler_LCNF_toImpureType___closed__0));
v___x_1144_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(v_declName_1142_, v___x_1143_, v_a_1139_, v_a_1140_);
return v___x_1144_;
}
case 5:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_Expr_getAppFn(v_type_1138_);
if (lean_obj_tag(v___x_1145_) == 4)
{
lean_object* v_declName_1146_; lean_object* v_dummy_1147_; lean_object* v_nargs_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_declName_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_declName_1146_);
lean_dec_ref_known(v___x_1145_, 2);
v_dummy_1147_ = lean_obj_once(&l_Lean_Compiler_LCNF_toImpureType___closed__1, &l_Lean_Compiler_LCNF_toImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_toImpureType___closed__1);
v_nargs_1148_ = l_Lean_Expr_getAppNumArgs(v_type_1138_);
lean_inc(v_nargs_1148_);
v___x_1149_ = lean_mk_array(v_nargs_1148_, v_dummy_1147_);
v___x_1150_ = lean_unsigned_to_nat(1u);
v___x_1151_ = lean_nat_sub(v_nargs_1148_, v___x_1150_);
lean_dec(v_nargs_1148_);
v___x_1152_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_type_1138_, v___x_1149_, v___x_1151_);
v___x_1153_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(v_declName_1146_, v___x_1152_, v_a_1139_, v_a_1140_);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec_ref(v___x_1145_);
lean_dec_ref_known(v_type_1138_, 2);
v___x_1154_ = lean_obj_once(&l_Lean_Compiler_LCNF_toImpureType___closed__3, &l_Lean_Compiler_LCNF_toImpureType___closed__3_once, _init_l_Lean_Compiler_LCNF_toImpureType___closed__3);
v___x_1155_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(v___x_1154_, v_a_1139_, v_a_1140_);
return v___x_1155_;
}
}
case 7:
{
lean_object* v_body_1156_; uint8_t v___x_1157_; 
v_body_1156_ = lean_ctor_get(v_type_1138_, 2);
lean_inc_ref(v_body_1156_);
lean_dec_ref_known(v_type_1138_, 3);
v___x_1157_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(v_body_1156_);
lean_dec_ref(v_body_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2);
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
case 10:
{
lean_object* v_expr_1162_; 
v_expr_1162_ = lean_ctor_get(v_type_1138_, 1);
lean_inc_ref(v_expr_1162_);
lean_dec_ref_known(v_type_1138_, 2);
v_type_1138_ = v_expr_1162_;
goto _start;
}
default: 
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec_ref(v_type_1138_);
v___x_1164_ = lean_obj_once(&l_Lean_Compiler_LCNF_toImpureType___closed__4, &l_Lean_Compiler_LCNF_toImpureType___closed__4_once, _init_l_Lean_Compiler_LCNF_toImpureType___closed__4);
v___x_1165_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(v___x_1164_, v_a_1139_, v_a_1140_);
return v___x_1165_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(lean_object* v_declName_1166_, lean_object* v_args_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; 
lean_inc(v_declName_1166_);
v___x_1171_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_declName_1166_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_1171_, 1);
if (lean_obj_tag(v_a_1172_) == 1)
{
lean_object* v_val_1173_; lean_object* v_ctorName_1174_; lean_object* v_numParams_1175_; lean_object* v_fieldIdx_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec(v_declName_1166_);
v_val_1173_ = lean_ctor_get(v_a_1172_, 0);
lean_inc(v_val_1173_);
lean_dec_ref_known(v_a_1172_, 1);
v_ctorName_1174_ = lean_ctor_get(v_val_1173_, 0);
lean_inc(v_ctorName_1174_);
v_numParams_1175_ = lean_ctor_get(v_val_1173_, 1);
lean_inc(v_numParams_1175_);
v_fieldIdx_1176_ = lean_ctor_get(v_val_1173_, 2);
lean_inc(v_fieldIdx_1176_);
lean_dec(v_val_1173_);
v___x_1177_ = lean_box(0);
v___x_1178_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_ctorName_1174_, v___x_1177_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1178_, 1);
v___x_1180_ = lean_unsigned_to_nat(0u);
v___x_1181_ = l_Array_toSubarray___redArg(v_args_1167_, v___x_1180_, v_numParams_1175_);
v___x_1182_ = l_Subarray_copy___redArg(v___x_1181_);
v___x_1183_ = l_Lean_Compiler_LCNF_instantiateForall(v_a_1179_, v___x_1182_, v_a_1168_, v_a_1169_);
lean_dec_ref(v___x_1182_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = l_Lean_instInhabitedExpr;
v___x_1186_ = l_Lean_Compiler_LCNF_getParamTypes(v_a_1184_);
v___x_1187_ = lean_array_get(v___x_1185_, v___x_1186_, v_fieldIdx_1176_);
lean_dec(v_fieldIdx_1176_);
lean_dec_ref(v___x_1186_);
v___x_1188_ = l_Lean_Compiler_LCNF_toMonoType(v___x_1187_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1190_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
v___x_1190_ = l_Lean_Compiler_LCNF_toImpureType(v_a_1189_, v_a_1168_, v_a_1169_);
return v___x_1190_;
}
else
{
return v___x_1188_;
}
}
else
{
lean_dec(v_fieldIdx_1176_);
return v___x_1183_;
}
}
else
{
lean_dec(v_fieldIdx_1176_);
lean_dec(v_numParams_1175_);
lean_dec_ref(v_args_1167_);
return v___x_1178_;
}
}
else
{
lean_object* v___x_1191_; 
lean_dec(v_a_1172_);
lean_dec_ref(v_args_1167_);
v___x_1191_ = l_Lean_Compiler_LCNF_nameToImpureType(v_declName_1166_, v_a_1168_, v_a_1169_);
return v___x_1191_;
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v_args_1167_);
lean_dec(v_declName_1166_);
v_a_1192_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1171_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1171_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp___boxed(lean_object* v_declName_1200_, lean_object* v_args_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(v_declName_1200_, v_args_1201_, v_a_1202_, v_a_1203_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpureType___boxed(lean_object* v_type_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1206_, v_a_1207_, v_a_1208_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx(lean_object* v_x_1211_){
_start:
{
switch(lean_obj_tag(v_x_1211_))
{
case 0:
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_unsigned_to_nat(0u);
return v___x_1212_;
}
case 1:
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_unsigned_to_nat(1u);
return v___x_1213_;
}
case 2:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_unsigned_to_nat(2u);
return v___x_1214_;
}
case 3:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_unsigned_to_nat(3u);
return v___x_1215_;
}
default: 
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_unsigned_to_nat(4u);
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx___boxed(lean_object* v_x_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx(v_x_1217_);
lean_dec(v_x_1217_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(lean_object* v_t_1219_, lean_object* v_k_1220_){
_start:
{
switch(lean_obj_tag(v_t_1219_))
{
case 1:
{
lean_object* v_i_1221_; lean_object* v_type_1222_; lean_object* v___x_1223_; 
v_i_1221_ = lean_ctor_get(v_t_1219_, 0);
lean_inc(v_i_1221_);
v_type_1222_ = lean_ctor_get(v_t_1219_, 1);
lean_inc_ref(v_type_1222_);
lean_dec_ref_known(v_t_1219_, 2);
v___x_1223_ = lean_apply_2(v_k_1220_, v_i_1221_, v_type_1222_);
return v___x_1223_;
}
case 2:
{
lean_object* v_i_1224_; lean_object* v___x_1225_; 
v_i_1224_ = lean_ctor_get(v_t_1219_, 0);
lean_inc(v_i_1224_);
lean_dec_ref_known(v_t_1219_, 1);
v___x_1225_ = lean_apply_1(v_k_1220_, v_i_1224_);
return v___x_1225_;
}
case 3:
{
lean_object* v_sz_1226_; lean_object* v_offset_1227_; lean_object* v_type_1228_; lean_object* v___x_1229_; 
v_sz_1226_ = lean_ctor_get(v_t_1219_, 0);
lean_inc(v_sz_1226_);
v_offset_1227_ = lean_ctor_get(v_t_1219_, 1);
lean_inc(v_offset_1227_);
v_type_1228_ = lean_ctor_get(v_t_1219_, 2);
lean_inc_ref(v_type_1228_);
lean_dec_ref_known(v_t_1219_, 3);
v___x_1229_ = lean_apply_3(v_k_1220_, v_sz_1226_, v_offset_1227_, v_type_1228_);
return v___x_1229_;
}
default: 
{
lean_dec(v_t_1219_);
return v_k_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim(lean_object* v_motive_1230_, lean_object* v_ctorIdx_1231_, lean_object* v_t_1232_, lean_object* v_h_1233_, lean_object* v_k_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1232_, v_k_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___boxed(lean_object* v_motive_1236_, lean_object* v_ctorIdx_1237_, lean_object* v_t_1238_, lean_object* v_h_1239_, lean_object* v_k_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim(v_motive_1236_, v_ctorIdx_1237_, v_t_1238_, v_h_1239_, v_k_1240_);
lean_dec(v_ctorIdx_1237_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_erased_elim___redArg(lean_object* v_t_1242_, lean_object* v_erased_1243_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1242_, v_erased_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_erased_elim(lean_object* v_motive_1245_, lean_object* v_t_1246_, lean_object* v_h_1247_, lean_object* v_erased_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1246_, v_erased_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_object_elim___redArg(lean_object* v_t_1250_, lean_object* v_object_1251_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1250_, v_object_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_object_elim(lean_object* v_motive_1253_, lean_object* v_t_1254_, lean_object* v_h_1255_, lean_object* v_object_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1254_, v_object_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_usize_elim___redArg(lean_object* v_t_1258_, lean_object* v_usize_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1258_, v_usize_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_usize_elim(lean_object* v_motive_1261_, lean_object* v_t_1262_, lean_object* v_h_1263_, lean_object* v_usize_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1262_, v_usize_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_scalar_elim___redArg(lean_object* v_t_1266_, lean_object* v_scalar_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1266_, v_scalar_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_scalar_elim(lean_object* v_motive_1269_, lean_object* v_t_1270_, lean_object* v_h_1271_, lean_object* v_scalar_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1270_, v_scalar_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_void_elim___redArg(lean_object* v_t_1274_, lean_object* v_void_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1274_, v_void_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_void_elim(lean_object* v_motive_1277_, lean_object* v_t_1278_, lean_object* v_h_1279_, lean_object* v_void_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1278_, v_void_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo_default(void){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_box(0);
return v___x_1282_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo(void){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_box(0);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format(lean_object* v_x_1305_){
_start:
{
switch(lean_obj_tag(v_x_1305_))
{
case 0:
{
lean_object* v___x_1306_; 
v___x_1306_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__1));
return v___x_1306_;
}
case 1:
{
lean_object* v_i_1307_; lean_object* v_type_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1323_; 
v_i_1307_ = lean_ctor_get(v_x_1305_, 0);
v_type_1308_ = lean_ctor_get(v_x_1305_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_x_1305_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1310_ = v_x_1305_;
v_isShared_1311_ = v_isSharedCheck_1323_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_type_1308_);
lean_inc(v_i_1307_);
lean_dec(v_x_1305_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1323_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1312_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__3));
v___x_1313_ = l_Nat_reprFast(v_i_1307_);
v___x_1314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set_tag(v___x_1310_, 5);
lean_ctor_set(v___x_1310_, 1, v___x_1314_);
lean_ctor_set(v___x_1310_, 0, v___x_1312_);
v___x_1316_ = v___x_1310_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1317_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5));
v___x_1318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1316_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___x_1319_ = lean_expr_dbg_to_string(v_type_1308_);
lean_dec_ref(v_type_1308_);
v___x_1320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
v___x_1321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1318_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
return v___x_1321_;
}
}
}
case 2:
{
lean_object* v_i_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1334_; 
v_i_1324_ = lean_ctor_get(v_x_1305_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_x_1305_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1326_ = v_x_1305_;
v_isShared_1327_ = v_isSharedCheck_1334_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_i_1324_);
lean_dec(v_x_1305_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1334_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1328_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__7));
v___x_1329_ = l_Nat_reprFast(v_i_1324_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set_tag(v___x_1326_, 3);
lean_ctor_set(v___x_1326_, 0, v___x_1329_);
v___x_1331_ = v___x_1326_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1328_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
return v___x_1332_;
}
}
}
case 3:
{
lean_object* v_sz_1335_; lean_object* v_offset_1336_; lean_object* v_type_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_sz_1335_ = lean_ctor_get(v_x_1305_, 0);
lean_inc(v_sz_1335_);
v_offset_1336_ = lean_ctor_get(v_x_1305_, 1);
lean_inc(v_offset_1336_);
v_type_1337_ = lean_ctor_get(v_x_1305_, 2);
lean_inc_ref(v_type_1337_);
lean_dec_ref_known(v_x_1305_, 3);
v___x_1338_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__9));
v___x_1339_ = l_Nat_reprFast(v_sz_1335_);
v___x_1340_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
v___x_1341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1338_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
v___x_1342_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__11));
v___x_1343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1341_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
v___x_1344_ = l_Nat_reprFast(v_offset_1336_);
v___x_1345_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
v___x_1346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1343_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5));
v___x_1348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = lean_expr_dbg_to_string(v_type_1337_);
lean_dec_ref(v_type_1337_);
v___x_1350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
v___x_1351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1348_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
return v___x_1351_;
}
default: 
{
lean_object* v___x_1352_; 
v___x_1352_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__13));
return v___x_1352_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1357_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0));
v___x_1358_ = l_Lean_Compiler_LCNF_instInhabitedCtorInfo_default;
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v___x_1357_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default(void){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1);
return v___x_1360_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout(void){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(lean_object* v_env_1362_, lean_object* v_as_1363_, size_t v_i_1364_, size_t v_stop_1365_, lean_object* v_b_1366_){
_start:
{
lean_object* v___y_1368_; uint8_t v___x_1372_; 
v___x_1372_ = lean_usize_dec_eq(v_i_1364_, v_stop_1365_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v_fst_1374_; uint8_t v___x_1375_; 
v___x_1373_ = lean_array_uget_borrowed(v_as_1363_, v_i_1364_);
v_fst_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_fst_1374_);
lean_inc_ref(v_env_1362_);
v___x_1375_ = l_Lean_Environment_contains(v_env_1362_, v_fst_1374_, v___x_1372_);
if (v___x_1375_ == 0)
{
v___y_1368_ = v_b_1366_;
goto v___jp_1367_;
}
else
{
lean_object* v___x_1376_; 
lean_inc(v___x_1373_);
v___x_1376_ = lean_array_push(v_b_1366_, v___x_1373_);
v___y_1368_ = v___x_1376_;
goto v___jp_1367_;
}
}
else
{
lean_dec_ref(v_env_1362_);
return v_b_1366_;
}
v___jp_1367_:
{
size_t v___x_1369_; size_t v___x_1370_; 
v___x_1369_ = ((size_t)1ULL);
v___x_1370_ = lean_usize_add(v_i_1364_, v___x_1369_);
v_i_1364_ = v___x_1370_;
v_b_1366_ = v___y_1368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_1377_, lean_object* v_as_1378_, lean_object* v_i_1379_, lean_object* v_stop_1380_, lean_object* v_b_1381_){
_start:
{
size_t v_i_boxed_1382_; size_t v_stop_boxed_1383_; lean_object* v_res_1384_; 
v_i_boxed_1382_ = lean_unbox_usize(v_i_1379_);
lean_dec(v_i_1379_);
v_stop_boxed_1383_ = lean_unbox_usize(v_stop_1380_);
lean_dec(v_stop_1380_);
v_res_1384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(v_env_1377_, v_as_1378_, v_i_boxed_1382_, v_stop_boxed_1383_, v_b_1381_);
lean_dec_ref(v_as_1378_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_1385_, lean_object* v_x_1386_){
_start:
{
if (lean_obj_tag(v_x_1386_) == 0)
{
lean_object* v_k_1387_; lean_object* v_v_1388_; lean_object* v_l_1389_; lean_object* v_r_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_k_1387_ = lean_ctor_get(v_x_1386_, 1);
v_v_1388_ = lean_ctor_get(v_x_1386_, 2);
v_l_1389_ = lean_ctor_get(v_x_1386_, 3);
v_r_1390_ = lean_ctor_get(v_x_1386_, 4);
v___x_1391_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0_spec__0(v_init_1385_, v_l_1389_);
lean_inc(v_v_1388_);
lean_inc(v_k_1387_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v_k_1387_);
lean_ctor_set(v___x_1392_, 1, v_v_1388_);
v___x_1393_ = lean_array_push(v___x_1391_, v___x_1392_);
v_init_1385_ = v___x_1393_;
v_x_1386_ = v_r_1390_;
goto _start;
}
else
{
return v_init_1385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_1395_, lean_object* v_x_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0_spec__0(v_init_1395_, v_x_1396_);
lean_dec(v_x_1396_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(lean_object* v___x_1398_, lean_object* v_env_1399_, lean_object* v_s_1400_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1401_ = lean_mk_empty_array_with_capacity(v___x_1398_);
v___x_1402_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0_spec__0(v___x_1401_, v_s_1400_);
v___x_1403_ = lean_array_get_size(v___x_1402_);
v___x_1404_ = lean_mk_empty_array_with_capacity(v___x_1398_);
v___x_1405_ = lean_nat_dec_lt(v___x_1398_, v___x_1403_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; 
lean_dec_ref(v___x_1402_);
lean_dec_ref(v_env_1399_);
lean_inc_ref_n(v___x_1404_, 2);
v___x_1406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1404_);
lean_ctor_set(v___x_1406_, 1, v___x_1404_);
lean_ctor_set(v___x_1406_, 2, v___x_1404_);
return v___x_1406_;
}
else
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_nat_dec_le(v___x_1403_, v___x_1403_);
if (v___x_1407_ == 0)
{
if (v___x_1405_ == 0)
{
lean_object* v___x_1408_; 
lean_dec_ref(v___x_1402_);
lean_dec_ref(v_env_1399_);
lean_inc_ref_n(v___x_1404_, 2);
v___x_1408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1404_);
lean_ctor_set(v___x_1408_, 1, v___x_1404_);
lean_ctor_set(v___x_1408_, 2, v___x_1404_);
return v___x_1408_;
}
else
{
size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = lean_usize_of_nat(v___x_1403_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(v_env_1399_, v___x_1402_, v___x_1409_, v___x_1410_, v___x_1404_);
lean_dec_ref(v___x_1402_);
lean_inc_ref_n(v___x_1411_, 2);
v___x_1412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
lean_ctor_set(v___x_1412_, 2, v___x_1411_);
return v___x_1412_;
}
}
else
{
size_t v___x_1413_; size_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1413_ = ((size_t)0ULL);
v___x_1414_ = lean_usize_of_nat(v___x_1403_);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(v_env_1399_, v___x_1402_, v___x_1413_, v___x_1414_, v___x_1404_);
lean_dec_ref(v___x_1402_);
lean_inc_ref_n(v___x_1415_, 2);
v___x_1416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
lean_ctor_set(v___x_1416_, 2, v___x_1415_);
return v___x_1416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2____boxed(lean_object* v___x_1417_, lean_object* v_env_1418_, lean_object* v_s_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(v___x_1417_, v_env_1418_, v_s_1419_);
lean_dec(v_s_1419_);
lean_dec(v___x_1417_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___f_1428_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_));
v___x_1429_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_));
v___x_1430_ = lean_box(0);
v___x_1431_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_1429_, v___x_1430_, v___f_1428_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2____boxed(lean_object* v_a_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_();
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(lean_object* v_init_1434_, lean_object* v_t_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0_spec__0(v_init_1434_, v_t_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_1437_, lean_object* v_t_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(v_init_1437_, v_t_1438_);
lean_dec(v_t_1438_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(lean_object* v_msg_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___f_1444_; lean_object* v___x_11568__overap_1445_; lean_object* v___x_1446_; 
v___f_1444_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0));
v___x_11568__overap_1445_ = lean_panic_fn_borrowed(v___f_1444_, v_msg_1440_);
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
v___x_1446_ = lean_apply_3(v___x_11568__overap_1445_, v___y_1441_, v___y_1442_, lean_box(0));
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1___boxed(lean_object* v_msg_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(v_msg_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(lean_object* v_msg_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___f_1459_; lean_object* v___x_11578__overap_1460_; lean_object* v___x_1461_; 
v___f_1459_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___closed__0));
v___x_11578__overap_1460_ = lean_panic_fn_borrowed(v___f_1459_, v_msg_1453_);
lean_inc(v___y_1457_);
lean_inc_ref(v___y_1456_);
lean_inc(v___y_1455_);
lean_inc_ref(v___y_1454_);
v___x_1461_ = lean_apply_5(v___x_11578__overap_1460_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, lean_box(0));
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___boxed(lean_object* v_msg_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(v_msg_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg(lean_object* v_type_1469_, lean_object* v_k_1470_, uint8_t v_cleanupAnnotations_1471_, uint8_t v_whnfType_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___f_1478_; lean_object* v___x_1479_; 
v___f_1478_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1478_, 0, v_k_1470_);
v___x_1479_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1469_, v___f_1478_, v_cleanupAnnotations_1471_, v_whnfType_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
v_a_1488_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1479_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1479_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg___boxed(lean_object* v_type_1496_, lean_object* v_k_1497_, lean_object* v_cleanupAnnotations_1498_, lean_object* v_whnfType_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1505_; uint8_t v_whnfType_boxed_1506_; lean_object* v_res_1507_; 
v_cleanupAnnotations_boxed_1505_ = lean_unbox(v_cleanupAnnotations_1498_);
v_whnfType_boxed_1506_ = lean_unbox(v_whnfType_1499_);
v_res_1507_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg(v_type_1496_, v_k_1497_, v_cleanupAnnotations_boxed_1505_, v_whnfType_boxed_1506_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5(lean_object* v_00_u03b1_1508_, lean_object* v_type_1509_, lean_object* v_k_1510_, uint8_t v_cleanupAnnotations_1511_, uint8_t v_whnfType_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg(v_type_1509_, v_k_1510_, v_cleanupAnnotations_1511_, v_whnfType_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___boxed(lean_object* v_00_u03b1_1519_, lean_object* v_type_1520_, lean_object* v_k_1521_, lean_object* v_cleanupAnnotations_1522_, lean_object* v_whnfType_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1529_; uint8_t v_whnfType_boxed_1530_; lean_object* v_res_1531_; 
v_cleanupAnnotations_boxed_1529_ = lean_unbox(v_cleanupAnnotations_1522_);
v_whnfType_boxed_1530_ = lean_unbox(v_whnfType_1523_);
v_res_1531_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5(v_00_u03b1_1519_, v_type_1520_, v_k_1521_, v_cleanupAnnotations_boxed_1529_, v_whnfType_boxed_1530_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(lean_object* v_size_1532_, size_t v_sz_1533_, size_t v_i_1534_, lean_object* v_bs_1535_, lean_object* v___y_1536_){
_start:
{
uint8_t v___x_1537_; 
v___x_1537_ = lean_usize_dec_lt(v_i_1534_, v_sz_1533_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v_bs_1535_);
lean_ctor_set(v___x_1538_, 1, v___y_1536_);
return v___x_1538_;
}
else
{
lean_object* v_v_1539_; lean_object* v___x_1540_; lean_object* v_bs_x27_1541_; lean_object* v_fst_1543_; lean_object* v_snd_1544_; 
v_v_1539_ = lean_array_uget(v_bs_1535_, v_i_1534_);
v___x_1540_ = lean_unsigned_to_nat(0u);
v_bs_x27_1541_ = lean_array_uset(v_bs_1535_, v_i_1534_, v___x_1540_);
switch(lean_obj_tag(v_v_1539_))
{
case 1:
{
v_fst_1543_ = v_v_1539_;
v_snd_1544_ = v___y_1536_;
goto v___jp_1542_;
}
case 2:
{
v_fst_1543_ = v_v_1539_;
v_snd_1544_ = v___y_1536_;
goto v___jp_1542_;
}
case 3:
{
lean_object* v_sz_1549_; lean_object* v_type_1550_; uint8_t v___x_1551_; 
v_sz_1549_ = lean_ctor_get(v_v_1539_, 0);
v_type_1550_ = lean_ctor_get(v_v_1539_, 2);
v___x_1551_ = lean_nat_dec_eq(v_sz_1549_, v_size_1532_);
if (v___x_1551_ == 0)
{
v_fst_1543_ = v_v_1539_;
v_snd_1544_ = v___y_1536_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1559_; 
lean_inc_ref(v_type_1550_);
lean_inc(v_sz_1549_);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_v_1539_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; lean_object* v_unused_1561_; lean_object* v_unused_1562_; 
v_unused_1560_ = lean_ctor_get(v_v_1539_, 2);
lean_dec(v_unused_1560_);
v_unused_1561_ = lean_ctor_get(v_v_1539_, 1);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_v_1539_, 0);
lean_dec(v_unused_1562_);
v___x_1553_ = v_v_1539_;
v_isShared_1554_ = v_isSharedCheck_1559_;
goto v_resetjp_1552_;
}
else
{
lean_dec(v_v_1539_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1559_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1555_ = lean_nat_add(v___y_1536_, v_sz_1549_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 1, v___y_1536_);
v___x_1557_ = v___x_1553_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_sz_1549_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v___y_1536_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_type_1550_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
v_fst_1543_ = v___x_1557_;
v_snd_1544_ = v___x_1555_;
goto v___jp_1542_;
}
}
}
}
default: 
{
v_fst_1543_ = v_v_1539_;
v_snd_1544_ = v___y_1536_;
goto v___jp_1542_;
}
}
v___jp_1542_:
{
size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = ((size_t)1ULL);
v___x_1546_ = lean_usize_add(v_i_1534_, v___x_1545_);
v___x_1547_ = lean_array_uset(v_bs_x27_1541_, v_i_1534_, v_fst_1543_);
v_i_1534_ = v___x_1546_;
v_bs_1535_ = v___x_1547_;
v___y_1536_ = v_snd_1544_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0___boxed(lean_object* v_size_1563_, lean_object* v_sz_1564_, lean_object* v_i_1565_, lean_object* v_bs_1566_, lean_object* v___y_1567_){
_start:
{
size_t v_sz_boxed_1568_; size_t v_i_boxed_1569_; lean_object* v_res_1570_; 
v_sz_boxed_1568_ = lean_unbox_usize(v_sz_1564_);
lean_dec(v_sz_1564_);
v_i_boxed_1569_ = lean_unbox_usize(v_i_1565_);
lean_dec(v_i_1565_);
v_res_1570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(v_size_1563_, v_sz_boxed_1568_, v_i_boxed_1569_, v_bs_1566_, v___y_1567_);
lean_dec(v_size_1563_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0(lean_object* v_fields_1571_, lean_object* v_size_1572_, lean_object* v_nextOffset_1573_){
_start:
{
size_t v_sz_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
v_sz_1574_ = lean_array_size(v_fields_1571_);
v___x_1575_ = ((size_t)0ULL);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(v_size_1572_, v_sz_1574_, v___x_1575_, v_fields_1571_, v_nextOffset_1573_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0___boxed(lean_object* v_fields_1577_, lean_object* v_size_1578_, lean_object* v_nextOffset_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0(v_fields_1577_, v_size_1578_, v_nextOffset_1579_);
lean_dec(v_size_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(size_t v_sz_1581_, size_t v_i_1582_, lean_object* v_bs_1583_, lean_object* v___y_1584_){
_start:
{
uint8_t v___x_1585_; 
v___x_1585_ = lean_usize_dec_lt(v_i_1582_, v_sz_1581_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_bs_1583_);
lean_ctor_set(v___x_1586_, 1, v___y_1584_);
return v___x_1586_;
}
else
{
lean_object* v_v_1587_; lean_object* v___x_1588_; lean_object* v_bs_x27_1589_; lean_object* v_fst_1591_; lean_object* v_snd_1592_; 
v_v_1587_ = lean_array_uget(v_bs_1583_, v_i_1582_);
v___x_1588_ = lean_unsigned_to_nat(0u);
v_bs_x27_1589_ = lean_array_uset(v_bs_1583_, v_i_1582_, v___x_1588_);
switch(lean_obj_tag(v_v_1587_))
{
case 1:
{
v_fst_1591_ = v_v_1587_;
v_snd_1592_ = v___y_1584_;
goto v___jp_1590_;
}
case 2:
{
lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1605_; 
v_isSharedCheck_1605_ = !lean_is_exclusive(v_v_1587_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v_v_1587_, 0);
lean_dec(v_unused_1606_);
v___x_1598_ = v_v_1587_;
v_isShared_1599_ = v_isSharedCheck_1605_;
goto v_resetjp_1597_;
}
else
{
lean_dec(v_v_1587_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1605_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1600_ = lean_unsigned_to_nat(1u);
v___x_1601_ = lean_nat_add(v___y_1584_, v___x_1600_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___y_1584_);
v___x_1603_ = v___x_1598_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___y_1584_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
v_fst_1591_ = v___x_1603_;
v_snd_1592_ = v___x_1601_;
goto v___jp_1590_;
}
}
}
case 3:
{
v_fst_1591_ = v_v_1587_;
v_snd_1592_ = v___y_1584_;
goto v___jp_1590_;
}
default: 
{
v_fst_1591_ = v_v_1587_;
v_snd_1592_ = v___y_1584_;
goto v___jp_1590_;
}
}
v___jp_1590_:
{
size_t v___x_1593_; size_t v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = ((size_t)1ULL);
v___x_1594_ = lean_usize_add(v_i_1582_, v___x_1593_);
v___x_1595_ = lean_array_uset(v_bs_x27_1589_, v_i_1582_, v_fst_1591_);
v_i_1582_ = v___x_1594_;
v_bs_1583_ = v___x_1595_;
v___y_1584_ = v_snd_1592_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4___boxed(lean_object* v_sz_1607_, lean_object* v_i_1608_, lean_object* v_bs_1609_, lean_object* v___y_1610_){
_start:
{
size_t v_sz_boxed_1611_; size_t v_i_boxed_1612_; lean_object* v_res_1613_; 
v_sz_boxed_1611_ = lean_unbox_usize(v_sz_1607_);
lean_dec(v_sz_1607_);
v_i_boxed_1612_ = lean_unbox_usize(v_i_1608_);
lean_dec(v_i_1608_);
v_res_1613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(v_sz_boxed_1611_, v_i_boxed_1612_, v_bs_1609_, v___y_1610_);
return v_res_1613_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1615_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_1616_ = lean_unsigned_to_nat(13u);
v___x_1617_ = lean_unsigned_to_nat(233u);
v___x_1618_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0));
v___x_1619_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_1620_ = l_mkPanicMessageWithDecl(v___x_1619_, v___x_1618_, v___x_1617_, v___x_1616_, v___x_1615_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(lean_object* v___f_1621_, lean_object* v_fst_1622_, lean_object* v_fst_1623_, lean_object* v_fst_1624_, lean_object* v_fst_1625_, lean_object* v_snd_1626_, lean_object* v_x_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1);
v___x_1634_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(v___x_1633_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1636_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1634_, 1);
lean_inc(v___y_1631_);
lean_inc_ref(v___y_1630_);
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
v___x_1636_ = lean_apply_11(v___f_1621_, v_a_1635_, v_fst_1622_, v_fst_1623_, v_fst_1624_, v_fst_1625_, v_snd_1626_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, lean_box(0));
return v___x_1636_;
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec(v_snd_1626_);
lean_dec(v_fst_1625_);
lean_dec(v_fst_1624_);
lean_dec(v_fst_1623_);
lean_dec(v_fst_1622_);
lean_dec_ref(v___f_1621_);
v_a_1637_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1634_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1634_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___boxed(lean_object* v___f_1645_, lean_object* v_fst_1646_, lean_object* v_fst_1647_, lean_object* v_fst_1648_, lean_object* v_fst_1649_, lean_object* v_snd_1650_, lean_object* v_x_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1645_, v_fst_1646_, v_fst_1647_, v_fst_1648_, v_fst_1649_, v_snd_1650_, v_x_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec_ref(v_x_1651_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(lean_object* v_fst_1658_, lean_object* v_ctorField_1659_, lean_object* v_nextIdx_1660_, uint8_t v_has1BScalar_1661_, uint8_t v_has2BScalar_1662_, uint8_t v_has4BScalar_1663_, uint8_t v_has8BScalar_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1670_ = lean_array_push(v_fst_1658_, v_ctorField_1659_);
v___x_1671_ = lean_box(v_has4BScalar_1663_);
v___x_1672_ = lean_box(v_has8BScalar_1664_);
v___x_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = lean_box(v_has2BScalar_1662_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v___x_1673_);
v___x_1676_ = lean_box(v_has1BScalar_1661_);
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v___x_1675_);
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v_nextIdx_1660_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1670_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0___boxed(lean_object* v_fst_1682_, lean_object* v_ctorField_1683_, lean_object* v_nextIdx_1684_, lean_object* v_has1BScalar_1685_, lean_object* v_has2BScalar_1686_, lean_object* v_has4BScalar_1687_, lean_object* v_has8BScalar_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
uint8_t v_has1BScalar_boxed_1694_; uint8_t v_has2BScalar_boxed_1695_; uint8_t v_has4BScalar_boxed_1696_; uint8_t v_has8BScalar_boxed_1697_; lean_object* v_res_1698_; 
v_has1BScalar_boxed_1694_ = lean_unbox(v_has1BScalar_1685_);
v_has2BScalar_boxed_1695_ = lean_unbox(v_has2BScalar_1686_);
v_has4BScalar_boxed_1696_ = lean_unbox(v_has4BScalar_1687_);
v_has8BScalar_boxed_1697_ = lean_unbox(v_has8BScalar_1688_);
v_res_1698_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1682_, v_ctorField_1683_, v_nextIdx_1684_, v_has1BScalar_boxed_1694_, v_has2BScalar_boxed_1695_, v_has4BScalar_boxed_1696_, v_has8BScalar_boxed_1697_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(lean_object* v_fst_1699_, lean_object* v___x_1700_, lean_object* v_a_1701_, lean_object* v___f_1702_, lean_object* v_fst_1703_, lean_object* v_fst_1704_, lean_object* v_fst_1705_, lean_object* v_snd_1706_, lean_object* v_00___1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = lean_nat_add(v_fst_1699_, v___x_1700_);
v___x_1714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_fst_1699_);
lean_ctor_set(v___x_1714_, 1, v_a_1701_);
lean_inc(v___y_1711_);
lean_inc_ref(v___y_1710_);
lean_inc(v___y_1709_);
lean_inc_ref(v___y_1708_);
v___x_1715_ = lean_apply_11(v___f_1702_, v___x_1714_, v___x_1713_, v_fst_1703_, v_fst_1704_, v_fst_1705_, v_snd_1706_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, lean_box(0));
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2___boxed(lean_object* v_fst_1716_, lean_object* v___x_1717_, lean_object* v_a_1718_, lean_object* v___f_1719_, lean_object* v_fst_1720_, lean_object* v_fst_1721_, lean_object* v_fst_1722_, lean_object* v_snd_1723_, lean_object* v_00___1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1716_, v___x_1717_, v_a_1718_, v___f_1719_, v_fst_1720_, v_fst_1721_, v_fst_1722_, v_snd_1723_, v_00___1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___x_1717_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(lean_object* v_a_1733_, lean_object* v_b_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_array_1740_; lean_object* v_start_1741_; lean_object* v_stop_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1967_; 
v_array_1740_ = lean_ctor_get(v_a_1733_, 0);
v_start_1741_ = lean_ctor_get(v_a_1733_, 1);
v_stop_1742_ = lean_ctor_get(v_a_1733_, 2);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_a_1733_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1744_ = v_a_1733_;
v_isShared_1745_ = v_isSharedCheck_1967_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_stop_1742_);
lean_inc(v_start_1741_);
lean_inc(v_array_1740_);
lean_dec(v_a_1733_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1967_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
uint8_t v___x_1746_; 
v___x_1746_ = lean_nat_dec_lt(v_start_1741_, v_stop_1742_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; 
lean_del_object(v___x_1744_);
lean_dec(v_stop_1742_);
lean_dec(v_start_1741_);
lean_dec_ref(v_array_1740_);
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v_b_1734_);
return v___x_1747_;
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1748_ = lean_array_fget_borrowed(v_array_1740_, v_start_1741_);
v___x_1749_ = l_Lean_Expr_fvarId_x21(v___x_1748_);
v___x_1750_ = l_Lean_FVarId_getType___redArg(v___x_1749_, v___y_1735_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v___x_1752_ = l_Lean_Compiler_LCNF_toLCNFType(v_a_1751_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = l_Lean_Compiler_LCNF_toMonoType(v_a_1753_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1756_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = l_Lean_Compiler_LCNF_toImpureType(v_a_1755_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_snd_1757_; lean_object* v_snd_1758_; lean_object* v_snd_1759_; lean_object* v_snd_1760_; lean_object* v_a_1761_; lean_object* v_fst_1762_; lean_object* v_fst_1763_; lean_object* v_fst_1764_; lean_object* v_fst_1765_; lean_object* v_fst_1766_; lean_object* v_snd_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v_snd_1757_ = lean_ctor_get(v_b_1734_, 1);
lean_inc(v_snd_1757_);
v_snd_1758_ = lean_ctor_get(v_snd_1757_, 1);
lean_inc(v_snd_1758_);
v_snd_1759_ = lean_ctor_get(v_snd_1758_, 1);
lean_inc(v_snd_1759_);
v_snd_1760_ = lean_ctor_get(v_snd_1759_, 1);
lean_inc(v_snd_1760_);
v_a_1761_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1756_, 1);
v_fst_1762_ = lean_ctor_get(v_b_1734_, 0);
lean_inc(v_fst_1762_);
lean_dec_ref(v_b_1734_);
v_fst_1763_ = lean_ctor_get(v_snd_1757_, 0);
lean_inc(v_fst_1763_);
lean_dec(v_snd_1757_);
v_fst_1764_ = lean_ctor_get(v_snd_1758_, 0);
lean_inc(v_fst_1764_);
lean_dec(v_snd_1758_);
v_fst_1765_ = lean_ctor_get(v_snd_1759_, 0);
lean_inc(v_fst_1765_);
lean_dec(v_snd_1759_);
v_fst_1766_ = lean_ctor_get(v_snd_1760_, 0);
lean_inc(v_fst_1766_);
v_snd_1767_ = lean_ctor_get(v_snd_1760_, 1);
lean_inc(v_snd_1767_);
lean_dec(v_snd_1760_);
v___x_1768_ = lean_unsigned_to_nat(1u);
v___x_1769_ = lean_nat_add(v_start_1741_, v___x_1768_);
lean_dec(v_start_1741_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 1, v___x_1769_);
v___x_1771_ = v___x_1744_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_array_1740_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1934_, 2, v_stop_1742_);
v___x_1771_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___y_1773_; lean_object* v___f_1793_; 
lean_inc(v_fst_1762_);
v___f_1793_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1793_, 0, v_fst_1762_);
if (lean_obj_tag(v_a_1761_) == 4)
{
lean_object* v_declName_1794_; 
v_declName_1794_ = lean_ctor_get(v_a_1761_, 0);
if (lean_obj_tag(v_declName_1794_) == 1)
{
lean_object* v_pre_1795_; 
v_pre_1795_ = lean_ctor_get(v_declName_1794_, 0);
if (lean_obj_tag(v_pre_1795_) == 0)
{
lean_object* v_us_1796_; lean_object* v_str_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v_us_1796_ = lean_ctor_get(v_a_1761_, 1);
v_str_1797_ = lean_ctor_get(v_declName_1794_, 1);
v___x_1798_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__0));
v___x_1799_ = lean_string_dec_eq(v_str_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__0));
v___x_1801_ = lean_string_dec_eq(v_str_1797_, v___x_1800_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__10));
v___x_1803_ = lean_string_dec_eq(v_str_1797_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1804_ = lean_unsigned_to_nat(0u);
v___x_1805_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__1));
v___x_1806_ = lean_string_dec_eq(v_str_1797_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__4));
v___x_1808_ = lean_string_dec_eq(v_str_1797_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__6));
v___x_1810_ = lean_string_dec_eq(v_str_1797_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9));
v___x_1812_ = lean_string_dec_eq(v_str_1797_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6));
v___x_1814_ = lean_string_dec_eq(v_str_1797_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1815_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3));
v___x_1816_ = lean_string_dec_eq(v_str_1797_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1817_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__0));
v___x_1818_ = lean_string_dec_eq(v_str_1797_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1819_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__3));
v___x_1820_ = lean_string_dec_eq(v_str_1797_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__2));
v___x_1822_ = lean_string_dec_eq(v_str_1797_, v___x_1821_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; 
lean_dec(v_fst_1762_);
v___x_1823_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v_a_1761_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref_known(v_a_1761_, 2);
v___y_1773_ = v___x_1823_;
goto v___jp_1772_;
}
else
{
lean_inc(v_pre_1795_);
lean_inc(v_us_1796_);
lean_dec_ref_known(v_a_1761_, 2);
if (lean_obj_tag(v_us_1796_) == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; uint8_t v___x_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; 
lean_dec_ref(v___f_1793_);
lean_dec(v_snd_1767_);
v___x_1824_ = lean_unsigned_to_nat(8u);
v___x_1825_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__20));
v___x_1826_ = l_Lean_Expr_const___override(v___x_1825_, v_us_1796_);
v___x_1827_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1824_);
lean_ctor_set(v___x_1827_, 1, v___x_1804_);
lean_ctor_set(v___x_1827_, 2, v___x_1826_);
v___x_1828_ = lean_unbox(v_fst_1764_);
lean_dec(v_fst_1764_);
v___x_1829_ = lean_unbox(v_fst_1765_);
lean_dec(v_fst_1765_);
v___x_1830_ = lean_unbox(v_fst_1766_);
lean_dec(v_fst_1766_);
v___x_1831_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1762_, v___x_1827_, v_fst_1763_, v___x_1828_, v___x_1829_, v___x_1830_, v___x_1822_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
v___y_1773_ = v___x_1831_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_dec(v_fst_1762_);
v___x_1832_ = l_Lean_Name_str___override(v_pre_1795_, v___x_1821_);
v___x_1833_ = l_Lean_Expr_const___override(v___x_1832_, v_us_1796_);
v___x_1834_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1833_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v___x_1833_);
v___y_1773_ = v___x_1834_;
goto v___jp_1772_;
}
}
}
else
{
lean_inc(v_pre_1795_);
lean_inc(v_us_1796_);
lean_dec_ref_known(v_a_1761_, 2);
if (lean_obj_tag(v_us_1796_) == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; uint8_t v___x_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; 
lean_dec_ref(v___f_1793_);
lean_dec(v_fst_1766_);
v___x_1835_ = lean_unsigned_to_nat(4u);
v___x_1836_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__17));
v___x_1837_ = l_Lean_Expr_const___override(v___x_1836_, v_us_1796_);
v___x_1838_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1835_);
lean_ctor_set(v___x_1838_, 1, v___x_1804_);
lean_ctor_set(v___x_1838_, 2, v___x_1837_);
v___x_1839_ = lean_unbox(v_fst_1764_);
lean_dec(v_fst_1764_);
v___x_1840_ = lean_unbox(v_fst_1765_);
lean_dec(v_fst_1765_);
v___x_1841_ = lean_unbox(v_snd_1767_);
lean_dec(v_snd_1767_);
v___x_1842_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1762_, v___x_1838_, v_fst_1763_, v___x_1839_, v___x_1840_, v___x_1820_, v___x_1841_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
v___y_1773_ = v___x_1842_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec(v_fst_1762_);
v___x_1843_ = l_Lean_Name_str___override(v_pre_1795_, v___x_1819_);
v___x_1844_ = l_Lean_Expr_const___override(v___x_1843_, v_us_1796_);
v___x_1845_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1844_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v___x_1844_);
v___y_1773_ = v___x_1845_;
goto v___jp_1772_;
}
}
}
else
{
lean_inc(v_pre_1795_);
lean_inc(v_us_1796_);
lean_dec_ref_known(v_a_1761_, 2);
if (lean_obj_tag(v_us_1796_) == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; uint8_t v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; 
lean_dec_ref(v___f_1793_);
lean_dec(v_snd_1767_);
v___x_1846_ = lean_unsigned_to_nat(8u);
v___x_1847_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__26));
v___x_1848_ = l_Lean_Expr_const___override(v___x_1847_, v_us_1796_);
v___x_1849_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1846_);
lean_ctor_set(v___x_1849_, 1, v___x_1804_);
lean_ctor_set(v___x_1849_, 2, v___x_1848_);
v___x_1850_ = lean_unbox(v_fst_1764_);
lean_dec(v_fst_1764_);
v___x_1851_ = lean_unbox(v_fst_1765_);
lean_dec(v_fst_1765_);
v___x_1852_ = lean_unbox(v_fst_1766_);
lean_dec(v_fst_1766_);
v___x_1853_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1762_, v___x_1849_, v_fst_1763_, v___x_1850_, v___x_1851_, v___x_1852_, v___x_1818_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
v___y_1773_ = v___x_1853_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec(v_fst_1762_);
v___x_1854_ = l_Lean_Name_str___override(v_pre_1795_, v___x_1817_);
v___x_1855_ = l_Lean_Expr_const___override(v___x_1854_, v_us_1796_);
v___x_1856_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1855_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v___x_1855_);
v___y_1773_ = v___x_1856_;
goto v___jp_1772_;
}
}
}
else
{
lean_inc(v_pre_1795_);
lean_inc(v_us_1796_);
lean_dec_ref_known(v_a_1761_, 2);
if (lean_obj_tag(v_us_1796_) == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; uint8_t v___x_1862_; uint8_t v___x_1863_; lean_object* v___x_1864_; 
lean_dec_ref(v___f_1793_);
lean_dec(v_fst_1766_);
v___x_1857_ = lean_unsigned_to_nat(4u);
v___x_1858_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__4));
v___x_1859_ = l_Lean_Expr_const___override(v___x_1858_, v_us_1796_);
v___x_1860_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1857_);
lean_ctor_set(v___x_1860_, 1, v___x_1804_);
lean_ctor_set(v___x_1860_, 2, v___x_1859_);
v___x_1861_ = lean_unbox(v_fst_1764_);
lean_dec(v_fst_1764_);
v___x_1862_ = lean_unbox(v_fst_1765_);
lean_dec(v_fst_1765_);
v___x_1863_ = lean_unbox(v_snd_1767_);
lean_dec(v_snd_1767_);
v___x_1864_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1762_, v___x_1860_, v_fst_1763_, v___x_1861_, v___x_1862_, v___x_1816_, v___x_1863_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
v___y_1773_ = v___x_1864_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_dec(v_fst_1762_);
v___x_1865_ = l_Lean_Name_str___override(v_pre_1795_, v___x_1815_);
v___x_1866_ = l_Lean_Expr_const___override(v___x_1865_, v_us_1796_);
v___x_1867_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1866_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v___x_1866_);
v___y_1773_ = v___x_1867_;
goto v___jp_1772_;
}
}
}
else
{
lean_inc(v_pre_1795_);
lean_inc(v_us_1796_);
lean_dec_ref_known(v_a_1761_, 2);
if (lean_obj_tag(v_us_1796_) == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; uint8_t v___x_1873_; uint8_t v___x_1874_; lean_object* v___x_1875_; 
lean_dec_ref(v___f_1793_);
lean_dec(v_fst_1765_);
v___x_1868_ = lean_unsigned_to_nat(2u);
v___x_1869_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__7));
v___x_1870_ = l_Lean_Expr_const___override(v___x_1869_, v_us_1796_);
v___x_1871_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1868_);
lean_ctor_set(v___x_1871_, 1, v___x_1804_);
lean_ctor_set(v___x_1871_, 2, v___x_1870_);
v___x_1872_ = lean_unbox(v_fst_1764_);
lean_dec(v_fst_1764_);
v___x_1873_ = lean_unbox(v_fst_1766_);
lean_dec(v_fst_1766_);
v___x_1874_ = lean_unbox(v_snd_1767_);
lean_dec(v_snd_1767_);
v___x_1875_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1762_, v___x_1871_, v_fst_1763_, v___x_1872_, v___x_1814_, v___x_1873_, v___x_1874_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
v___y_1773_ = v___x_1875_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec(v_fst_1762_);
v___x_1876_ = l_Lean_Name_str___override(v_pre_1795_, v___x_1813_);
v___x_1877_ = l_Lean_Expr_const___override(v___x_1876_, v_us_1796_);
v___x_1878_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1877_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v___x_1877_);
v___y_1773_ = v___x_1878_;
goto v___jp_1772_;
}
}
}
else
{
lean_inc(v_pre_1795_);
lean_inc(v_us_1796_);
lean_dec_ref_known(v_a_1761_, 2);
if (lean_obj_tag(v_us_1796_) == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; uint8_t v___x_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; 
lean_dec_ref(v___f_1793_);
lean_dec(v_fst_1764_);
v___x_1879_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__10));
v___x_1880_ = l_Lean_Expr_const___override(v___x_1879_, v_us_1796_);
v___x_1881_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1768_);
lean_ctor_set(v___x_1881_, 1, v___x_1804_);
lean_ctor_set(v___x_1881_, 2, v___x_1880_);
v___x_1882_ = lean_unbox(v_fst_1765_);
lean_dec(v_fst_1765_);
v___x_1883_ = lean_unbox(v_fst_1766_);
lean_dec(v_fst_1766_);
v___x_1884_ = lean_unbox(v_snd_1767_);
lean_dec(v_snd_1767_);
v___x_1885_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1762_, v___x_1881_, v_fst_1763_, v___x_1812_, v___x_1882_, v___x_1883_, v___x_1884_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
v___y_1773_ = v___x_1885_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec(v_fst_1762_);
v___x_1886_ = l_Lean_Name_str___override(v_pre_1795_, v___x_1811_);
v___x_1887_ = l_Lean_Expr_const___override(v___x_1886_, v_us_1796_);
v___x_1888_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1887_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v___x_1887_);
v___y_1773_ = v___x_1888_;
goto v___jp_1772_;
}
}
}
else
{
lean_inc(v_pre_1795_);
lean_inc(v_us_1796_);
lean_dec_ref_known(v_a_1761_, 2);
if (lean_obj_tag(v_us_1796_) == 0)
{
lean_object* v___x_1889_; uint8_t v___x_1890_; uint8_t v___x_1891_; uint8_t v___x_1892_; uint8_t v___x_1893_; lean_object* v___x_1894_; 
lean_dec_ref(v___f_1793_);
v___x_1889_ = lean_box(4);
v___x_1890_ = lean_unbox(v_fst_1764_);
lean_dec(v_fst_1764_);
v___x_1891_ = lean_unbox(v_fst_1765_);
lean_dec(v_fst_1765_);
v___x_1892_ = lean_unbox(v_fst_1766_);
lean_dec(v_fst_1766_);
v___x_1893_ = lean_unbox(v_snd_1767_);
lean_dec(v_snd_1767_);
v___x_1894_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1762_, v___x_1889_, v_fst_1763_, v___x_1890_, v___x_1891_, v___x_1892_, v___x_1893_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
v___y_1773_ = v___x_1894_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec(v_fst_1762_);
v___x_1895_ = l_Lean_Name_str___override(v_pre_1795_, v___x_1809_);
v___x_1896_ = l_Lean_Expr_const___override(v___x_1895_, v_us_1796_);
v___x_1897_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1896_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v___x_1896_);
v___y_1773_ = v___x_1897_;
goto v___jp_1772_;
}
}
}
else
{
lean_inc(v_pre_1795_);
lean_inc(v_us_1796_);
lean_dec_ref_known(v_a_1761_, 2);
if (lean_obj_tag(v_us_1796_) == 0)
{
lean_object* v___x_1898_; uint8_t v___x_1899_; uint8_t v___x_1900_; uint8_t v___x_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; 
lean_dec_ref(v___f_1793_);
v___x_1898_ = lean_box(0);
v___x_1899_ = lean_unbox(v_fst_1764_);
lean_dec(v_fst_1764_);
v___x_1900_ = lean_unbox(v_fst_1765_);
lean_dec(v_fst_1765_);
v___x_1901_ = lean_unbox(v_fst_1766_);
lean_dec(v_fst_1766_);
v___x_1902_ = lean_unbox(v_snd_1767_);
lean_dec(v_snd_1767_);
v___x_1903_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1762_, v___x_1898_, v_fst_1763_, v___x_1899_, v___x_1900_, v___x_1901_, v___x_1902_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
v___y_1773_ = v___x_1903_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_dec(v_fst_1762_);
v___x_1904_ = l_Lean_Name_str___override(v_pre_1795_, v___x_1807_);
v___x_1905_ = l_Lean_Expr_const___override(v___x_1904_, v_us_1796_);
v___x_1906_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1905_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v___x_1905_);
v___y_1773_ = v___x_1906_;
goto v___jp_1772_;
}
}
}
else
{
lean_inc(v_pre_1795_);
lean_inc(v_us_1796_);
lean_dec_ref_known(v_a_1761_, 2);
if (lean_obj_tag(v_us_1796_) == 0)
{
lean_object* v___x_1907_; uint8_t v___x_1908_; uint8_t v___x_1909_; uint8_t v___x_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; 
lean_dec_ref(v___f_1793_);
v___x_1907_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___closed__0));
v___x_1908_ = lean_unbox(v_fst_1764_);
lean_dec(v_fst_1764_);
v___x_1909_ = lean_unbox(v_fst_1765_);
lean_dec(v_fst_1765_);
v___x_1910_ = lean_unbox(v_fst_1766_);
lean_dec(v_fst_1766_);
v___x_1911_ = lean_unbox(v_snd_1767_);
lean_dec(v_snd_1767_);
v___x_1912_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1762_, v___x_1907_, v_fst_1763_, v___x_1908_, v___x_1909_, v___x_1910_, v___x_1911_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
v___y_1773_ = v___x_1912_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
lean_dec(v_fst_1762_);
v___x_1913_ = l_Lean_Name_str___override(v_pre_1795_, v___x_1805_);
v___x_1914_ = l_Lean_Expr_const___override(v___x_1913_, v_us_1796_);
v___x_1915_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1914_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v___x_1914_);
v___y_1773_ = v___x_1915_;
goto v___jp_1772_;
}
}
}
else
{
lean_dec(v_fst_1762_);
if (lean_obj_tag(v_us_1796_) == 0)
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_box(0);
v___x_1917_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1763_, v___x_1768_, v_a_1761_, v___f_1793_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1916_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
v___y_1773_ = v___x_1917_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_inc(v_pre_1795_);
lean_inc(v_us_1796_);
lean_dec_ref_known(v_a_1761_, 2);
v___x_1918_ = l_Lean_Name_str___override(v_pre_1795_, v___x_1802_);
v___x_1919_ = l_Lean_Expr_const___override(v___x_1918_, v_us_1796_);
v___x_1920_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1919_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v___x_1919_);
v___y_1773_ = v___x_1920_;
goto v___jp_1772_;
}
}
}
else
{
lean_dec(v_fst_1762_);
if (lean_obj_tag(v_us_1796_) == 0)
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = lean_box(0);
v___x_1922_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1763_, v___x_1768_, v_a_1761_, v___f_1793_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1921_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
v___y_1773_ = v___x_1922_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
lean_inc(v_pre_1795_);
lean_inc(v_us_1796_);
lean_dec_ref_known(v_a_1761_, 2);
v___x_1923_ = l_Lean_Name_str___override(v_pre_1795_, v___x_1800_);
v___x_1924_ = l_Lean_Expr_const___override(v___x_1923_, v_us_1796_);
v___x_1925_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1924_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v___x_1924_);
v___y_1773_ = v___x_1925_;
goto v___jp_1772_;
}
}
}
else
{
lean_dec(v_fst_1762_);
if (lean_obj_tag(v_us_1796_) == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_box(0);
v___x_1927_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1763_, v___x_1768_, v_a_1761_, v___f_1793_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1926_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
v___y_1773_ = v___x_1927_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
lean_inc(v_pre_1795_);
lean_inc(v_us_1796_);
lean_dec_ref_known(v_a_1761_, 2);
v___x_1928_ = l_Lean_Name_str___override(v_pre_1795_, v___x_1798_);
v___x_1929_ = l_Lean_Expr_const___override(v___x_1928_, v_us_1796_);
v___x_1930_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v___x_1929_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v___x_1929_);
v___y_1773_ = v___x_1930_;
goto v___jp_1772_;
}
}
}
else
{
lean_object* v___x_1931_; 
lean_dec(v_fst_1762_);
v___x_1931_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v_a_1761_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref_known(v_a_1761_, 2);
v___y_1773_ = v___x_1931_;
goto v___jp_1772_;
}
}
else
{
lean_object* v___x_1932_; 
lean_dec(v_fst_1762_);
v___x_1932_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v_a_1761_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref_known(v_a_1761_, 2);
v___y_1773_ = v___x_1932_;
goto v___jp_1772_;
}
}
else
{
lean_object* v___x_1933_; 
lean_dec(v_fst_1762_);
v___x_1933_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1793_, v_fst_1763_, v_fst_1764_, v_fst_1765_, v_fst_1766_, v_snd_1767_, v_a_1761_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v_a_1761_);
v___y_1773_ = v___x_1933_;
goto v___jp_1772_;
}
v___jp_1772_:
{
if (lean_obj_tag(v___y_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1784_; 
v_a_1774_ = lean_ctor_get(v___y_1773_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___y_1773_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1776_ = v___y_1773_;
v_isShared_1777_ = v_isSharedCheck_1784_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___y_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1784_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
if (lean_obj_tag(v_a_1774_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; 
lean_dec_ref(v___x_1771_);
v_a_1778_ = lean_ctor_get(v_a_1774_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v_a_1774_, 1);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v_a_1778_);
v___x_1780_ = v___x_1776_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
else
{
lean_object* v_a_1782_; 
lean_del_object(v___x_1776_);
v_a_1782_ = lean_ctor_get(v_a_1774_, 0);
lean_inc(v_a_1782_);
lean_dec_ref_known(v_a_1774_, 1);
v_a_1733_ = v___x_1771_;
v_b_1734_ = v_a_1782_;
goto _start;
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec_ref(v___x_1771_);
v_a_1785_ = lean_ctor_get(v___y_1773_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___y_1773_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___y_1773_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___y_1773_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_del_object(v___x_1744_);
lean_dec(v_stop_1742_);
lean_dec(v_start_1741_);
lean_dec_ref(v_array_1740_);
lean_dec_ref(v_b_1734_);
v_a_1935_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1756_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1756_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_del_object(v___x_1744_);
lean_dec(v_stop_1742_);
lean_dec(v_start_1741_);
lean_dec_ref(v_array_1740_);
lean_dec_ref(v_b_1734_);
v_a_1943_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1754_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1754_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_del_object(v___x_1744_);
lean_dec(v_stop_1742_);
lean_dec(v_start_1741_);
lean_dec_ref(v_array_1740_);
lean_dec_ref(v_b_1734_);
v_a_1951_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1752_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1752_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_del_object(v___x_1744_);
lean_dec(v_stop_1742_);
lean_dec(v_start_1741_);
lean_dec_ref(v_array_1740_);
lean_dec_ref(v_b_1734_);
v_a_1959_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1750_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1750_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___boxed(lean_object* v_a_1968_, lean_object* v_b_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v_a_1968_, v_b_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1(lean_object* v_numFields_1976_, lean_object* v_numParams_1977_, uint8_t v___x_1978_, lean_object* v_ctorName_1979_, lean_object* v_cidx_1980_, lean_object* v___f_1981_, lean_object* v_params_1982_, lean_object* v_x_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1989_ = lean_mk_empty_array_with_capacity(v_numFields_1976_);
v___x_1990_ = lean_unsigned_to_nat(0u);
v___x_1991_ = lean_nat_add(v_numParams_1977_, v_numFields_1976_);
v___x_1992_ = l_Array_toSubarray___redArg(v_params_1982_, v_numParams_1977_, v___x_1991_);
v___x_1993_ = lean_box(v___x_1978_);
v___x_1994_ = lean_box(v___x_1978_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = lean_box(v___x_1978_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v___x_1995_);
v___x_1998_ = lean_box(v___x_1978_);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
lean_ctor_set(v___x_1999_, 1, v___x_1997_);
v___x_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1990_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1989_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v___x_1992_, v___x_2001_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2066_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2066_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2066_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v_snd_2007_; lean_object* v_fst_2008_; lean_object* v_fst_2009_; lean_object* v_snd_2010_; size_t v_sz_2011_; size_t v___x_2012_; lean_object* v___x_2013_; lean_object* v_snd_2014_; lean_object* v_snd_2015_; lean_object* v_fst_2016_; lean_object* v_snd_2017_; lean_object* v_fst_2018_; lean_object* v_fst_2019_; lean_object* v_fst_2020_; lean_object* v_snd_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2065_; 
v_snd_2007_ = lean_ctor_get(v_a_2003_, 1);
lean_inc(v_snd_2007_);
v_fst_2008_ = lean_ctor_get(v_a_2003_, 0);
lean_inc(v_fst_2008_);
lean_dec(v_a_2003_);
v_fst_2009_ = lean_ctor_get(v_snd_2007_, 0);
lean_inc_n(v_fst_2009_, 2);
v_snd_2010_ = lean_ctor_get(v_snd_2007_, 1);
lean_inc(v_snd_2010_);
lean_dec(v_snd_2007_);
v_sz_2011_ = lean_array_size(v_fst_2008_);
v___x_2012_ = ((size_t)0ULL);
v___x_2013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(v_sz_2011_, v___x_2012_, v_fst_2008_, v_fst_2009_);
v_snd_2014_ = lean_ctor_get(v_snd_2010_, 1);
lean_inc(v_snd_2014_);
v_snd_2015_ = lean_ctor_get(v_snd_2014_, 1);
lean_inc(v_snd_2015_);
v_fst_2016_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_fst_2016_);
v_snd_2017_ = lean_ctor_get(v___x_2013_, 1);
lean_inc(v_snd_2017_);
lean_dec_ref(v___x_2013_);
v_fst_2018_ = lean_ctor_get(v_snd_2010_, 0);
lean_inc(v_fst_2018_);
lean_dec(v_snd_2010_);
v_fst_2019_ = lean_ctor_get(v_snd_2014_, 0);
lean_inc(v_fst_2019_);
lean_dec(v_snd_2014_);
v_fst_2020_ = lean_ctor_get(v_snd_2015_, 0);
v_snd_2021_ = lean_ctor_get(v_snd_2015_, 1);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_snd_2015_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2023_ = v_snd_2015_;
v_isShared_2024_ = v_isSharedCheck_2065_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_snd_2021_);
lean_inc(v_fst_2020_);
lean_dec(v_snd_2015_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2065_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v_fields_2027_; lean_object* v_nextOffset_2028_; lean_object* v_fields_2037_; lean_object* v_nextOffset_2038_; lean_object* v_fields_2045_; lean_object* v_nextOffset_2046_; lean_object* v_fields_2053_; lean_object* v_nextOffset_2054_; uint8_t v___x_2060_; 
v___x_2025_ = lean_nat_sub(v_snd_2017_, v_fst_2009_);
lean_dec(v_snd_2017_);
v___x_2060_ = lean_unbox(v_snd_2021_);
lean_dec(v_snd_2021_);
if (v___x_2060_ == 0)
{
v_fields_2053_ = v_fst_2016_;
v_nextOffset_2054_ = v___x_1990_;
goto v___jp_2052_;
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v_fst_2063_; lean_object* v_snd_2064_; 
v___x_2061_ = lean_unsigned_to_nat(8u);
lean_inc_ref(v___f_1981_);
v___x_2062_ = lean_apply_3(v___f_1981_, v_fst_2016_, v___x_2061_, v___x_1990_);
v_fst_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_fst_2063_);
v_snd_2064_ = lean_ctor_get(v___x_2062_, 1);
lean_inc(v_snd_2064_);
lean_dec_ref(v___x_2062_);
v_fields_2053_ = v_fst_2063_;
v_nextOffset_2054_ = v_snd_2064_;
goto v___jp_2052_;
}
v___jp_2026_:
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2029_, 0, v_ctorName_1979_);
lean_ctor_set(v___x_2029_, 1, v_cidx_1980_);
lean_ctor_set(v___x_2029_, 2, v_fst_2009_);
lean_ctor_set(v___x_2029_, 3, v___x_2025_);
lean_ctor_set(v___x_2029_, 4, v_nextOffset_2028_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 1, v_fields_2027_);
lean_ctor_set(v___x_2023_, 0, v___x_2029_);
v___x_2031_ = v___x_2023_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_fields_2027_);
v___x_2031_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2033_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2031_);
v___x_2033_ = v___x_2005_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
v___jp_2036_:
{
uint8_t v___x_2039_; 
v___x_2039_ = lean_unbox(v_fst_2018_);
lean_dec(v_fst_2018_);
if (v___x_2039_ == 0)
{
lean_dec_ref(v___f_1981_);
v_fields_2027_ = v_fields_2037_;
v_nextOffset_2028_ = v_nextOffset_2038_;
goto v___jp_2026_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v_fst_2042_; lean_object* v_snd_2043_; 
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_apply_3(v___f_1981_, v_fields_2037_, v___x_2040_, v_nextOffset_2038_);
v_fst_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_fst_2042_);
v_snd_2043_ = lean_ctor_get(v___x_2041_, 1);
lean_inc(v_snd_2043_);
lean_dec_ref(v___x_2041_);
v_fields_2027_ = v_fst_2042_;
v_nextOffset_2028_ = v_snd_2043_;
goto v___jp_2026_;
}
}
v___jp_2044_:
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_unbox(v_fst_2019_);
lean_dec(v_fst_2019_);
if (v___x_2047_ == 0)
{
v_fields_2037_ = v_fields_2045_;
v_nextOffset_2038_ = v_nextOffset_2046_;
goto v___jp_2036_;
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v_fst_2050_; lean_object* v_snd_2051_; 
v___x_2048_ = lean_unsigned_to_nat(2u);
lean_inc_ref(v___f_1981_);
v___x_2049_ = lean_apply_3(v___f_1981_, v_fields_2045_, v___x_2048_, v_nextOffset_2046_);
v_fst_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_fst_2050_);
v_snd_2051_ = lean_ctor_get(v___x_2049_, 1);
lean_inc(v_snd_2051_);
lean_dec_ref(v___x_2049_);
v_fields_2037_ = v_fst_2050_;
v_nextOffset_2038_ = v_snd_2051_;
goto v___jp_2036_;
}
}
v___jp_2052_:
{
uint8_t v___x_2055_; 
v___x_2055_ = lean_unbox(v_fst_2020_);
lean_dec(v_fst_2020_);
if (v___x_2055_ == 0)
{
v_fields_2045_ = v_fields_2053_;
v_nextOffset_2046_ = v_nextOffset_2054_;
goto v___jp_2044_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v_fst_2058_; lean_object* v_snd_2059_; 
v___x_2056_ = lean_unsigned_to_nat(4u);
lean_inc_ref(v___f_1981_);
v___x_2057_ = lean_apply_3(v___f_1981_, v_fields_2053_, v___x_2056_, v_nextOffset_2054_);
v_fst_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_fst_2058_);
v_snd_2059_ = lean_ctor_get(v___x_2057_, 1);
lean_inc(v_snd_2059_);
lean_dec_ref(v___x_2057_);
v_fields_2045_ = v_fst_2058_;
v_nextOffset_2046_ = v_snd_2059_;
goto v___jp_2044_;
}
}
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec_ref(v___f_1981_);
lean_dec(v_cidx_1980_);
lean_dec(v_ctorName_1979_);
v_a_2067_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2002_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2002_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___boxed(lean_object* v_numFields_2075_, lean_object* v_numParams_2076_, lean_object* v___x_2077_, lean_object* v_ctorName_2078_, lean_object* v_cidx_2079_, lean_object* v___f_2080_, lean_object* v_params_2081_, lean_object* v_x_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
uint8_t v___x_13731__boxed_2088_; lean_object* v_res_2089_; 
v___x_13731__boxed_2088_ = lean_unbox(v___x_2077_);
v_res_2089_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1(v_numFields_2075_, v_numParams_2076_, v___x_13731__boxed_2088_, v_ctorName_2078_, v_cidx_2079_, v___f_2080_, v_params_2081_, v_x_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec_ref(v_x_2082_);
lean_dec(v_numFields_2075_);
return v_res_2089_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2090_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_2091_ = lean_unsigned_to_nat(64u);
v___x_2092_ = lean_unsigned_to_nat(194u);
v___x_2093_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0));
v___x_2094_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_2095_ = l_mkPanicMessageWithDecl(v___x_2094_, v___x_2093_, v___x_2092_, v___x_2091_, v___x_2090_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(lean_object* v_ctorName_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___x_2106_; lean_object* v_env_2107_; uint8_t v___x_2108_; lean_object* v___x_2109_; 
v___x_2106_ = lean_st_ref_get(v_a_2099_);
v_env_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc_ref(v_env_2107_);
lean_dec(v___x_2106_);
v___x_2108_ = 0;
lean_inc(v_ctorName_2097_);
v___x_2109_ = l_Lean_Environment_find_x3f(v_env_2107_, v_ctorName_2097_, v___x_2108_);
if (lean_obj_tag(v___x_2109_) == 1)
{
lean_object* v_val_2110_; 
v_val_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_val_2110_);
lean_dec_ref_known(v___x_2109_, 1);
if (lean_obj_tag(v_val_2110_) == 6)
{
lean_object* v_val_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v_toConstantVal_2115_; lean_object* v_cidx_2116_; lean_object* v_numParams_2117_; lean_object* v_numFields_2118_; lean_object* v_type_2119_; lean_object* v___f_2120_; lean_object* v___x_2121_; lean_object* v___f_2122_; lean_object* v___x_2123_; 
v_val_2111_ = lean_ctor_get(v_val_2110_, 0);
lean_inc_ref(v_val_2111_);
lean_dec_ref_known(v_val_2110_, 1);
v___x_2112_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13);
v___x_2113_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17);
v___x_2114_ = lean_st_mk_ref(v___x_2113_);
v_toConstantVal_2115_ = lean_ctor_get(v_val_2111_, 0);
lean_inc_ref(v_toConstantVal_2115_);
v_cidx_2116_ = lean_ctor_get(v_val_2111_, 2);
lean_inc(v_cidx_2116_);
v_numParams_2117_ = lean_ctor_get(v_val_2111_, 3);
lean_inc(v_numParams_2117_);
v_numFields_2118_ = lean_ctor_get(v_val_2111_, 4);
lean_inc(v_numFields_2118_);
lean_dec_ref(v_val_2111_);
v_type_2119_ = lean_ctor_get(v_toConstantVal_2115_, 2);
lean_inc_ref(v_type_2119_);
lean_dec_ref(v_toConstantVal_2115_);
v___f_2120_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__1));
v___x_2121_ = lean_box(v___x_2108_);
v___f_2122_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___boxed), 13, 6);
lean_closure_set(v___f_2122_, 0, v_numFields_2118_);
lean_closure_set(v___f_2122_, 1, v_numParams_2117_);
lean_closure_set(v___f_2122_, 2, v___x_2121_);
lean_closure_set(v___f_2122_, 3, v_ctorName_2097_);
lean_closure_set(v___f_2122_, 4, v_cidx_2116_);
lean_closure_set(v___f_2122_, 5, v___f_2120_);
v___x_2123_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg(v_type_2119_, v___f_2122_, v___x_2108_, v___x_2108_, v___x_2112_, v___x_2114_, v_a_2098_, v_a_2099_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2132_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2132_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2132_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2128_ = lean_st_ref_get(v___x_2114_);
lean_dec(v___x_2114_);
lean_dec(v___x_2128_);
if (v_isShared_2127_ == 0)
{
v___x_2130_ = v___x_2126_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2124_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
else
{
lean_dec(v___x_2114_);
return v___x_2123_;
}
}
else
{
lean_dec(v_val_2110_);
lean_dec(v_ctorName_2097_);
v___y_2102_ = v_a_2098_;
v___y_2103_ = v_a_2099_;
goto v___jp_2101_;
}
}
else
{
lean_dec(v___x_2109_);
lean_dec(v_ctorName_2097_);
v___y_2102_ = v_a_2098_;
v___y_2103_ = v_a_2099_;
goto v___jp_2101_;
}
v___jp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0);
v___x_2105_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(v___x_2104_, v___y_2102_, v___y_2103_);
return v___x_2105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___boxed(lean_object* v_ctorName_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(v_ctorName_2133_, v_a_2134_, v_a_2135_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3(lean_object* v_inst_2138_, lean_object* v_R_2139_, lean_object* v_a_2140_, lean_object* v_b_2141_, lean_object* v_c_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v_a_2140_, v_b_2141_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___boxed(lean_object* v_inst_2149_, lean_object* v_R_2150_, lean_object* v_a_2151_, lean_object* v_b_2152_, lean_object* v_c_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3(v_inst_2149_, v_R_2150_, v_a_2151_, v_b_2152_, v_c_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setCtorLayout(lean_object* v_ctorName_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v___x_2164_; lean_object* v_env_2165_; lean_object* v___x_2166_; lean_object* v_toEnvExtension_2167_; lean_object* v_asyncMode_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; lean_object* v___x_2171_; 
v___x_2164_ = lean_st_ref_get(v_a_2162_);
v_env_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc_ref(v_env_2165_);
lean_dec(v___x_2164_);
v___x_2166_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt;
v_toEnvExtension_2167_ = lean_ctor_get(v___x_2166_, 0);
v_asyncMode_2168_ = lean_ctor_get(v_toEnvExtension_2167_, 2);
v___x_2169_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
v___x_2170_ = 0;
lean_inc(v_ctorName_2160_);
v___x_2171_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2169_, v___x_2166_, v_env_2165_, v_ctorName_2160_, v_asyncMode_2168_, v___x_2170_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v___x_2172_; 
lean_inc(v_ctorName_2160_);
v___x_2172_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(v_ctorName_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2201_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2201_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2201_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; lean_object* v_env_2178_; lean_object* v_nextMacroScope_2179_; lean_object* v_ngen_2180_; lean_object* v_auxDeclNGen_2181_; lean_object* v_traceState_2182_; lean_object* v_messages_2183_; lean_object* v_infoState_2184_; lean_object* v_snapshotTasks_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2199_; 
v___x_2177_ = lean_st_ref_take(v_a_2162_);
v_env_2178_ = lean_ctor_get(v___x_2177_, 0);
v_nextMacroScope_2179_ = lean_ctor_get(v___x_2177_, 1);
v_ngen_2180_ = lean_ctor_get(v___x_2177_, 2);
v_auxDeclNGen_2181_ = lean_ctor_get(v___x_2177_, 3);
v_traceState_2182_ = lean_ctor_get(v___x_2177_, 4);
v_messages_2183_ = lean_ctor_get(v___x_2177_, 6);
v_infoState_2184_ = lean_ctor_get(v___x_2177_, 7);
v_snapshotTasks_2185_ = lean_ctor_get(v___x_2177_, 8);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v___x_2177_, 5);
lean_dec(v_unused_2200_);
v___x_2187_ = v___x_2177_;
v_isShared_2188_ = v_isSharedCheck_2199_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_snapshotTasks_2185_);
lean_inc(v_infoState_2184_);
lean_inc(v_messages_2183_);
lean_inc(v_traceState_2182_);
lean_inc(v_auxDeclNGen_2181_);
lean_inc(v_ngen_2180_);
lean_inc(v_nextMacroScope_2179_);
lean_inc(v_env_2178_);
lean_dec(v___x_2177_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2199_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2189_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2166_, v_env_2178_, v_ctorName_2160_, v_a_2173_);
v___x_2190_ = lean_obj_once(&l_Lean_Compiler_LCNF_setImpureType___closed__2, &l_Lean_Compiler_LCNF_setImpureType___closed__2_once, _init_l_Lean_Compiler_LCNF_setImpureType___closed__2);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 5, v___x_2190_);
lean_ctor_set(v___x_2187_, 0, v___x_2189_);
v___x_2192_ = v___x_2187_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_nextMacroScope_2179_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_ngen_2180_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_auxDeclNGen_2181_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v_traceState_2182_);
lean_ctor_set(v_reuseFailAlloc_2198_, 5, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2198_, 6, v_messages_2183_);
lean_ctor_set(v_reuseFailAlloc_2198_, 7, v_infoState_2184_);
lean_ctor_set(v_reuseFailAlloc_2198_, 8, v_snapshotTasks_2185_);
v___x_2192_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2193_ = lean_st_ref_set(v_a_2162_, v___x_2192_);
v___x_2194_ = lean_box(0);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2194_);
v___x_2196_ = v___x_2175_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec(v_ctorName_2160_);
v_a_2202_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2172_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2172_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
else
{
lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v_ctorName_2160_);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2217_ == 0)
{
lean_object* v_unused_2218_; 
v_unused_2218_ = lean_ctor_get(v___x_2171_, 0);
lean_dec(v_unused_2218_);
v___x_2211_ = v___x_2171_;
v_isShared_2212_ = v_isSharedCheck_2217_;
goto v_resetjp_2210_;
}
else
{
lean_dec(v___x_2171_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2217_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2213_ = lean_box(0);
if (v_isShared_2212_ == 0)
{
lean_ctor_set_tag(v___x_2211_, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2213_);
v___x_2215_ = v___x_2211_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setCtorLayout___boxed(lean_object* v_ctorName_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_Compiler_LCNF_setCtorLayout(v_ctorName_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getCtorLayout(lean_object* v_ctorName_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v___x_2228_; lean_object* v_env_2229_; lean_object* v___x_2230_; lean_object* v_toEnvExtension_2231_; lean_object* v_asyncMode_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; lean_object* v___x_2235_; 
v___x_2228_ = lean_st_ref_get(v_a_2226_);
v_env_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc_ref(v_env_2229_);
lean_dec(v___x_2228_);
v___x_2230_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt;
v_toEnvExtension_2231_ = lean_ctor_get(v___x_2230_, 0);
v_asyncMode_2232_ = lean_ctor_get(v_toEnvExtension_2231_, 2);
v___x_2233_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
v___x_2234_ = 0;
lean_inc(v_ctorName_2224_);
v___x_2235_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2233_, v___x_2230_, v_env_2229_, v_ctorName_2224_, v_asyncMode_2232_, v___x_2234_);
if (lean_obj_tag(v___x_2235_) == 1)
{
lean_object* v_val_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec(v_ctorName_2224_);
v_val_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_val_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set_tag(v___x_2238_, 0);
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_val_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_dec(v___x_2235_);
v___x_2244_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__1, &l_Lean_Compiler_LCNF_nameToImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1);
v___x_2245_ = l_Lean_MessageData_ofName(v_ctorName_2224_);
v___x_2246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2244_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v___x_2247_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__3, &l_Lean_Compiler_LCNF_nameToImpureType___closed__3_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__3);
v___x_2248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2246_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
v___x_2249_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v___x_2248_, v_a_2225_, v_a_2226_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getCtorLayout___boxed(lean_object* v_ctorName_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_2250_, v_a_2251_, v_a_2252_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(lean_object* v_as_2255_, size_t v_sz_2256_, size_t v_i_2257_, lean_object* v_b_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
uint8_t v___x_2262_; 
v___x_2262_ = lean_usize_dec_lt(v_i_2257_, v_sz_2256_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; 
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v_b_2258_);
return v___x_2263_;
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2265_; 
v_a_2264_ = lean_array_uget_borrowed(v_as_2255_, v_i_2257_);
lean_inc(v_a_2264_);
v___x_2265_ = l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(v_a_2264_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v___x_2266_; 
lean_dec_ref_known(v___x_2265_, 1);
lean_inc(v_a_2264_);
v___x_2266_ = l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f(v_a_2264_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v___x_2267_; size_t v___x_2268_; size_t v___x_2269_; 
lean_dec_ref_known(v___x_2266_, 1);
v___x_2267_ = lean_box(0);
v___x_2268_ = ((size_t)1ULL);
v___x_2269_ = lean_usize_add(v_i_2257_, v___x_2268_);
v_i_2257_ = v___x_2269_;
v_b_2258_ = v___x_2267_;
goto _start;
}
else
{
return v___x_2266_;
}
}
else
{
return v___x_2265_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2___boxed(lean_object* v_as_2271_, lean_object* v_sz_2272_, lean_object* v_i_2273_, lean_object* v_b_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
size_t v_sz_boxed_2278_; size_t v_i_boxed_2279_; lean_object* v_res_2280_; 
v_sz_boxed_2278_ = lean_unbox_usize(v_sz_2272_);
lean_dec(v_sz_2272_);
v_i_boxed_2279_ = lean_unbox_usize(v_i_2273_);
lean_dec(v_i_2273_);
v_res_2280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(v_as_2271_, v_sz_boxed_2278_, v_i_boxed_2279_, v_b_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec_ref(v_as_2271_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(lean_object* v_as_x27_2281_, lean_object* v_b_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
if (lean_obj_tag(v_as_x27_2281_) == 0)
{
lean_object* v___x_2286_; 
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v_b_2282_);
return v___x_2286_;
}
else
{
lean_object* v_head_2287_; lean_object* v_tail_2288_; lean_object* v___x_2289_; 
v_head_2287_ = lean_ctor_get(v_as_x27_2281_, 0);
v_tail_2288_ = lean_ctor_get(v_as_x27_2281_, 1);
lean_inc(v_head_2287_);
v___x_2289_ = l_Lean_Compiler_LCNF_setOtherDeclMonoType(v_head_2287_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v___x_2290_; 
lean_dec_ref_known(v___x_2289_, 1);
lean_inc(v_head_2287_);
v___x_2290_ = l_Lean_Compiler_LCNF_setCtorLayout(v_head_2287_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v___x_2291_; 
lean_dec_ref_known(v___x_2290_, 1);
v___x_2291_ = lean_box(0);
v_as_x27_2281_ = v_tail_2288_;
v_b_2282_ = v___x_2291_;
goto _start;
}
else
{
return v___x_2290_;
}
}
else
{
return v___x_2289_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg___boxed(lean_object* v_as_x27_2293_, lean_object* v_b_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(v_as_x27_2293_, v_b_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v_as_x27_2293_);
return v_res_2298_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_2301_ = l_Lean_stringToMessageData(v___x_2300_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_2304_ = l_Lean_stringToMessageData(v___x_2303_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_2307_ = l_Lean_stringToMessageData(v___x_2306_);
return v___x_2307_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_2310_ = l_Lean_stringToMessageData(v___x_2309_);
return v___x_2310_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_2313_ = l_Lean_stringToMessageData(v___x_2312_);
return v___x_2313_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_2316_ = l_Lean_stringToMessageData(v___x_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_2319_ = l_Lean_stringToMessageData(v___x_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2320_, lean_object* v_declHint_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___x_2324_; lean_object* v_env_2325_; uint8_t v___y_2327_; uint8_t v___x_2383_; uint8_t v___x_2384_; 
v___x_2324_ = lean_st_ref_get(v___y_2322_);
v_env_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc_ref(v_env_2325_);
lean_dec(v___x_2324_);
v___x_2383_ = l_Lean_Name_isAnonymous(v_declHint_2321_);
v___x_2384_ = lean_bool_not(v___x_2383_);
if (v___x_2384_ == 0)
{
v___y_2327_ = v___x_2384_;
goto v___jp_2326_;
}
else
{
uint8_t v_isExporting_2385_; 
v_isExporting_2385_ = lean_ctor_get_uint8(v_env_2325_, sizeof(void*)*8);
v___y_2327_ = v_isExporting_2385_;
goto v___jp_2326_;
}
v___jp_2326_:
{
if (v___y_2327_ == 0)
{
lean_object* v___x_2328_; 
lean_dec_ref(v_env_2325_);
lean_dec(v_declHint_2321_);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_msg_2320_);
return v___x_2328_;
}
else
{
uint8_t v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2329_ = 0;
lean_inc_ref(v_env_2325_);
v___x_2330_ = l_Lean_Environment_setExporting(v_env_2325_, v___x_2329_);
lean_inc(v_declHint_2321_);
lean_inc_ref(v___x_2330_);
v___x_2331_ = l_Lean_Environment_contains(v___x_2330_, v_declHint_2321_, v___y_2327_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; 
lean_dec_ref(v___x_2330_);
lean_dec_ref(v_env_2325_);
lean_dec(v_declHint_2321_);
v___x_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2332_, 0, v_msg_2320_);
return v___x_2332_;
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v_c_2338_; lean_object* v___x_2339_; 
v___x_2333_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2);
v___x_2334_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__3);
v___x_2335_ = l_Lean_Options_empty;
v___x_2336_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2330_);
lean_ctor_set(v___x_2336_, 1, v___x_2333_);
lean_ctor_set(v___x_2336_, 2, v___x_2334_);
lean_ctor_set(v___x_2336_, 3, v___x_2335_);
lean_inc(v_declHint_2321_);
v___x_2337_ = l_Lean_MessageData_ofConstName(v_declHint_2321_, v___x_2329_);
v_c_2338_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2338_, 0, v___x_2336_);
lean_ctor_set(v_c_2338_, 1, v___x_2337_);
v___x_2339_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2325_, v_declHint_2321_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_dec_ref(v_env_2325_);
lean_dec(v_declHint_2321_);
v___x_2340_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
lean_ctor_set(v___x_2341_, 1, v_c_2338_);
v___x_2342_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_2343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2341_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
v___x_2344_ = l_Lean_MessageData_note(v___x_2343_);
v___x_2345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2345_, 0, v_msg_2320_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
return v___x_2346_;
}
else
{
lean_object* v_val_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2382_; 
v_val_2347_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2349_ = v___x_2339_;
v_isShared_2350_ = v_isSharedCheck_2382_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_val_2347_);
lean_dec(v___x_2339_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2382_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v_mod_2354_; uint8_t v___x_2355_; 
v___x_2351_ = lean_box(0);
v___x_2352_ = l_Lean_Environment_header(v_env_2325_);
lean_dec_ref(v_env_2325_);
v___x_2353_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2352_);
v_mod_2354_ = lean_array_get(v___x_2351_, v___x_2353_, v_val_2347_);
lean_dec(v_val_2347_);
lean_dec_ref(v___x_2353_);
v___x_2355_ = l_Lean_isPrivateName(v_declHint_2321_);
lean_dec(v_declHint_2321_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2356_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_2357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
lean_ctor_set(v___x_2357_, 1, v_c_2338_);
v___x_2358_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = l_Lean_MessageData_ofName(v_mod_2354_);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_2363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2361_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = l_Lean_MessageData_note(v___x_2363_);
v___x_2365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2365_, 0, v_msg_2320_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set_tag(v___x_2349_, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2365_);
v___x_2367_ = v___x_2349_;
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
else
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2369_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
lean_ctor_set(v___x_2370_, 1, v_c_2338_);
v___x_2371_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_2372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2370_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = l_Lean_MessageData_ofName(v_mod_2354_);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = l_Lean_MessageData_note(v___x_2376_);
v___x_2378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2378_, 0, v_msg_2320_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set_tag(v___x_2349_, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2378_);
v___x_2380_ = v___x_2349_;
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
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2386_, lean_object* v_declHint_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_2386_, v_declHint_2387_, v___y_2388_);
lean_dec(v___y_2388_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(lean_object* v_msg_2391_, lean_object* v_declHint_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2406_; 
v___x_2396_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_2391_, v_declHint_2392_, v___y_2394_);
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2406_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2406_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2401_ = l_Lean_unknownIdentifierMessageTag;
v___x_2402_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
lean_ctor_set(v___x_2402_, 1, v_a_2397_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2402_);
v___x_2404_ = v___x_2399_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8___boxed(lean_object* v_msg_2407_, lean_object* v_declHint_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_2407_, v_declHint_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(lean_object* v_ref_2413_, lean_object* v_msg_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_fileName_2418_; lean_object* v_fileMap_2419_; lean_object* v_options_2420_; lean_object* v_currRecDepth_2421_; lean_object* v_maxRecDepth_2422_; lean_object* v_ref_2423_; lean_object* v_currNamespace_2424_; lean_object* v_openDecls_2425_; lean_object* v_initHeartbeats_2426_; lean_object* v_maxHeartbeats_2427_; lean_object* v_quotContext_2428_; lean_object* v_currMacroScope_2429_; uint8_t v_diag_2430_; lean_object* v_cancelTk_x3f_2431_; uint8_t v_suppressElabErrors_2432_; lean_object* v_inheritedTraceOptions_2433_; lean_object* v_ref_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v_fileName_2418_ = lean_ctor_get(v___y_2415_, 0);
v_fileMap_2419_ = lean_ctor_get(v___y_2415_, 1);
v_options_2420_ = lean_ctor_get(v___y_2415_, 2);
v_currRecDepth_2421_ = lean_ctor_get(v___y_2415_, 3);
v_maxRecDepth_2422_ = lean_ctor_get(v___y_2415_, 4);
v_ref_2423_ = lean_ctor_get(v___y_2415_, 5);
v_currNamespace_2424_ = lean_ctor_get(v___y_2415_, 6);
v_openDecls_2425_ = lean_ctor_get(v___y_2415_, 7);
v_initHeartbeats_2426_ = lean_ctor_get(v___y_2415_, 8);
v_maxHeartbeats_2427_ = lean_ctor_get(v___y_2415_, 9);
v_quotContext_2428_ = lean_ctor_get(v___y_2415_, 10);
v_currMacroScope_2429_ = lean_ctor_get(v___y_2415_, 11);
v_diag_2430_ = lean_ctor_get_uint8(v___y_2415_, sizeof(void*)*14);
v_cancelTk_x3f_2431_ = lean_ctor_get(v___y_2415_, 12);
v_suppressElabErrors_2432_ = lean_ctor_get_uint8(v___y_2415_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2433_ = lean_ctor_get(v___y_2415_, 13);
v_ref_2434_ = l_Lean_replaceRef(v_ref_2413_, v_ref_2423_);
lean_inc_ref(v_inheritedTraceOptions_2433_);
lean_inc(v_cancelTk_x3f_2431_);
lean_inc(v_currMacroScope_2429_);
lean_inc(v_quotContext_2428_);
lean_inc(v_maxHeartbeats_2427_);
lean_inc(v_initHeartbeats_2426_);
lean_inc(v_openDecls_2425_);
lean_inc(v_currNamespace_2424_);
lean_inc(v_maxRecDepth_2422_);
lean_inc(v_currRecDepth_2421_);
lean_inc_ref(v_options_2420_);
lean_inc_ref(v_fileMap_2419_);
lean_inc_ref(v_fileName_2418_);
v___x_2435_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2435_, 0, v_fileName_2418_);
lean_ctor_set(v___x_2435_, 1, v_fileMap_2419_);
lean_ctor_set(v___x_2435_, 2, v_options_2420_);
lean_ctor_set(v___x_2435_, 3, v_currRecDepth_2421_);
lean_ctor_set(v___x_2435_, 4, v_maxRecDepth_2422_);
lean_ctor_set(v___x_2435_, 5, v_ref_2434_);
lean_ctor_set(v___x_2435_, 6, v_currNamespace_2424_);
lean_ctor_set(v___x_2435_, 7, v_openDecls_2425_);
lean_ctor_set(v___x_2435_, 8, v_initHeartbeats_2426_);
lean_ctor_set(v___x_2435_, 9, v_maxHeartbeats_2427_);
lean_ctor_set(v___x_2435_, 10, v_quotContext_2428_);
lean_ctor_set(v___x_2435_, 11, v_currMacroScope_2429_);
lean_ctor_set(v___x_2435_, 12, v_cancelTk_x3f_2431_);
lean_ctor_set(v___x_2435_, 13, v_inheritedTraceOptions_2433_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*14, v_diag_2430_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*14 + 1, v_suppressElabErrors_2432_);
v___x_2436_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_msg_2414_, v___x_2435_, v___y_2416_);
lean_dec_ref_known(v___x_2435_, 14);
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
v_ref_2484_ = lean_ctor_get(v___y_2481_, 5);
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
v___x_2516_ = lean_unsigned_to_nat(298u);
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
