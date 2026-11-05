// Lean compiler output
// Module: Lean.Compiler.LCNF.ToImpureType
// Imports: public import Lean.Compiler.LCNF.Irrelevant import Lean.Compiler.LCNF.MonoTypes import Lean.Runtime import Init.Data.Format.Macro
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Irrelevant_setHasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCtorInfo_default;
extern lean_object* l_Lean_maxCtorNumObjs;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclBaseType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getParamTypes(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CtorInfo_checkValid(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Subtype"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ST"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Void"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nonemptyType"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__4_value;
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
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___boxed(lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Compiler.LCNF.ToImpureType"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.computeImpureType"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__3;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__5;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__6;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__8;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__9;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__10;
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__11 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__11_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__12;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__13;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__15;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__16;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__17;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__18;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__19;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_setImpureType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_setImpureType___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_setImpureType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_setImpureType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setImpureType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setImpureType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_spilled_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_spilled_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__14 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__14_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__14_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__15 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_spillDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_spillDepth___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_spillLinkIdx___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_spillLinkIdx___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_spillLinkIdx;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_numSpillObjs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_numSpillObjs___boxed(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_spillCtorInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "spill"};
static const lean_object* l_Lean_Compiler_LCNF_spillCtorInfo___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_spillCtorInfo___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_spillCtorInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_spillCtorInfo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 44, 31, 101, 209, 151, 202, 87)}};
static const lean_object* l_Lean_Compiler_LCNF_spillCtorInfo___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_spillCtorInfo___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_spillCtorInfo(lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCtorLayout;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0(lean_object* v_env_41_, lean_object* v_as_42_, size_t v_i_43_, size_t v_stop_44_, lean_object* v_b_45_){
_start:
{
lean_object* v___y_47_; uint8_t v___x_51_; 
v___x_51_ = lean_usize_dec_eq(v_i_43_, v_stop_44_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v_fst_53_; uint8_t v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_52_ = lean_array_uget_borrowed(v_as_42_, v_i_43_);
v_fst_53_ = lean_ctor_get(v___x_52_, 0);
v___x_54_ = 1;
lean_inc_ref(v_env_41_);
v___x_55_ = l_Lean_Environment_setExporting(v_env_41_, v___x_54_);
lean_inc(v_fst_53_);
v___x_56_ = l_Lean_Environment_contains(v___x_55_, v_fst_53_, v___x_51_);
if (v___x_56_ == 0)
{
v___y_47_ = v_b_45_;
goto v___jp_46_;
}
else
{
lean_object* v___x_57_; 
lean_inc(v___x_52_);
v___x_57_ = lean_array_push(v_b_45_, v___x_52_);
v___y_47_ = v___x_57_;
goto v___jp_46_;
}
}
else
{
lean_dec_ref(v_env_41_);
return v_b_45_;
}
v___jp_46_:
{
size_t v___x_48_; size_t v___x_49_; 
v___x_48_ = ((size_t)1ULL);
v___x_49_ = lean_usize_add(v_i_43_, v___x_48_);
v_i_43_ = v___x_49_;
v_b_45_ = v___y_47_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_58_, lean_object* v_as_59_, lean_object* v_i_60_, lean_object* v_stop_61_, lean_object* v_b_62_){
_start:
{
size_t v_i_boxed_63_; size_t v_stop_boxed_64_; lean_object* v_res_65_; 
v_i_boxed_63_ = lean_unbox_usize(v_i_60_);
lean_dec(v_i_60_);
v_stop_boxed_64_ = lean_unbox_usize(v_stop_61_);
lean_dec(v_stop_61_);
v_res_65_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0(v_env_58_, v_as_59_, v_i_boxed_63_, v_stop_boxed_64_, v_b_62_);
lean_dec_ref(v_as_59_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_init_66_, lean_object* v_x_67_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
lean_object* v_k_68_; lean_object* v_v_69_; lean_object* v_l_70_; lean_object* v_r_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_k_68_ = lean_ctor_get(v_x_67_, 1);
v_v_69_ = lean_ctor_get(v_x_67_, 2);
v_l_70_ = lean_ctor_get(v_x_67_, 3);
v_r_71_ = lean_ctor_get(v_x_67_, 4);
v___x_72_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1_spec__1(v_init_66_, v_l_70_);
lean_inc(v_v_69_);
lean_inc(v_k_68_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v_k_68_);
lean_ctor_set(v___x_73_, 1, v_v_69_);
v___x_74_ = lean_array_push(v___x_72_, v___x_73_);
v_init_66_ = v___x_74_;
v_x_67_ = v_r_71_;
goto _start;
}
else
{
return v_init_66_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_init_76_, lean_object* v_x_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1_spec__1(v_init_76_, v_x_77_);
lean_dec(v_x_77_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__2(lean_object* v_env_79_, lean_object* v_as_80_, size_t v_i_81_, size_t v_stop_82_, lean_object* v_b_83_){
_start:
{
lean_object* v___y_85_; uint8_t v___x_89_; 
v___x_89_ = lean_usize_dec_eq(v_i_81_, v_stop_82_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; lean_object* v_fst_91_; uint8_t v___x_92_; 
v___x_90_ = lean_array_uget_borrowed(v_as_80_, v_i_81_);
v_fst_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_fst_91_);
lean_inc_ref(v_env_79_);
v___x_92_ = l_Lean_Environment_contains(v_env_79_, v_fst_91_, v___x_89_);
if (v___x_92_ == 0)
{
v___y_85_ = v_b_83_;
goto v___jp_84_;
}
else
{
lean_object* v___x_93_; 
lean_inc(v___x_90_);
v___x_93_ = lean_array_push(v_b_83_, v___x_90_);
v___y_85_ = v___x_93_;
goto v___jp_84_;
}
}
else
{
lean_dec_ref(v_env_79_);
return v_b_83_;
}
v___jp_84_:
{
size_t v___x_86_; size_t v___x_87_; 
v___x_86_ = ((size_t)1ULL);
v___x_87_ = lean_usize_add(v_i_81_, v___x_86_);
v_i_81_ = v___x_87_;
v_b_83_ = v___y_85_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_94_, lean_object* v_as_95_, lean_object* v_i_96_, lean_object* v_stop_97_, lean_object* v_b_98_){
_start:
{
size_t v_i_boxed_99_; size_t v_stop_boxed_100_; lean_object* v_res_101_; 
v_i_boxed_99_ = lean_unbox_usize(v_i_96_);
lean_dec(v_i_96_);
v_stop_boxed_100_ = lean_unbox_usize(v_stop_97_);
lean_dec(v_stop_97_);
v_res_101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__2(v_env_94_, v_as_95_, v_i_boxed_99_, v_stop_boxed_100_, v_b_98_);
lean_dec_ref(v_as_95_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_(lean_object* v___x_102_, lean_object* v_env_103_, lean_object* v_s_104_){
_start:
{
lean_object* v___y_106_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_115_ = lean_mk_empty_array_with_capacity(v___x_102_);
v___x_116_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1_spec__1(v___x_115_, v_s_104_);
v___x_117_ = lean_array_get_size(v___x_116_);
v___x_118_ = lean_mk_empty_array_with_capacity(v___x_102_);
v___x_119_ = lean_nat_dec_lt(v___x_102_, v___x_117_);
if (v___x_119_ == 0)
{
lean_dec_ref(v___x_116_);
v___y_106_ = v___x_118_;
goto v___jp_105_;
}
else
{
size_t v___x_120_; size_t v___x_121_; lean_object* v___x_122_; 
v___x_120_ = ((size_t)0ULL);
v___x_121_ = lean_usize_of_nat(v___x_117_);
lean_inc_ref(v_env_103_);
v___x_122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__2(v_env_103_, v___x_116_, v___x_120_, v___x_121_, v___x_118_);
lean_dec_ref(v___x_116_);
v___y_106_ = v___x_122_;
goto v___jp_105_;
}
v___jp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_107_ = lean_array_get_size(v___y_106_);
v___x_108_ = lean_mk_empty_array_with_capacity(v___x_102_);
v___x_109_ = lean_nat_dec_lt(v___x_102_, v___x_107_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
lean_dec_ref(v_env_103_);
lean_inc_ref(v___x_108_);
v___x_110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set(v___x_110_, 1, v___x_108_);
lean_ctor_set(v___x_110_, 2, v___y_106_);
return v___x_110_;
}
else
{
size_t v___x_111_; size_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_111_ = ((size_t)0ULL);
v___x_112_ = lean_usize_of_nat(v___x_107_);
v___x_113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0(v_env_103_, v___y_106_, v___x_111_, v___x_112_, v___x_108_);
lean_inc_ref(v___x_113_);
v___x_114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
lean_ctor_set(v___x_114_, 2, v___y_106_);
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2____boxed(lean_object* v___x_123_, lean_object* v_env_124_, lean_object* v_s_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_(v___x_123_, v_env_124_, v_s_125_);
lean_dec(v_s_125_);
lean_dec(v___x_123_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; lean_object* v___x_170_; 
v___f_166_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_));
v___x_167_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_));
v___x_168_ = lean_box(0);
v___x_169_ = 0;
v___x_170_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_167_, v___x_168_, v___x_169_, v___f_166_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2____boxed(lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_();
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1(lean_object* v_init_173_, lean_object* v_t_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1_spec__1(v_init_173_, v_t_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1___boxed(lean_object* v_init_176_, lean_object* v_t_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1(v_init_176_, v_t_177_);
lean_dec(v_t_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__2(lean_object* v_env_179_, lean_object* v_as_180_, size_t v_i_181_, size_t v_stop_182_, lean_object* v_b_183_){
_start:
{
lean_object* v___y_185_; uint8_t v___x_189_; 
v___x_189_ = lean_usize_dec_eq(v_i_181_, v_stop_182_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; lean_object* v_fst_191_; uint8_t v___x_192_; 
v___x_190_ = lean_array_uget_borrowed(v_as_180_, v_i_181_);
v_fst_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_fst_191_);
lean_inc_ref(v_env_179_);
v___x_192_ = l_Lean_Environment_contains(v_env_179_, v_fst_191_, v___x_189_);
if (v___x_192_ == 0)
{
v___y_185_ = v_b_183_;
goto v___jp_184_;
}
else
{
lean_object* v___x_193_; 
lean_inc(v___x_190_);
v___x_193_ = lean_array_push(v_b_183_, v___x_190_);
v___y_185_ = v___x_193_;
goto v___jp_184_;
}
}
else
{
lean_dec_ref(v_env_179_);
return v_b_183_;
}
v___jp_184_:
{
size_t v___x_186_; size_t v___x_187_; 
v___x_186_ = ((size_t)1ULL);
v___x_187_ = lean_usize_add(v_i_181_, v___x_186_);
v_i_181_ = v___x_187_;
v_b_183_ = v___y_185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_194_, lean_object* v_as_195_, lean_object* v_i_196_, lean_object* v_stop_197_, lean_object* v_b_198_){
_start:
{
size_t v_i_boxed_199_; size_t v_stop_boxed_200_; lean_object* v_res_201_; 
v_i_boxed_199_ = lean_unbox_usize(v_i_196_);
lean_dec(v_i_196_);
v_stop_boxed_200_ = lean_unbox_usize(v_stop_197_);
lean_dec(v_stop_197_);
v_res_201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__2(v_env_194_, v_as_195_, v_i_boxed_199_, v_stop_boxed_200_, v_b_198_);
lean_dec_ref(v_as_195_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_init_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
lean_object* v_k_204_; lean_object* v_v_205_; lean_object* v_l_206_; lean_object* v_r_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_k_204_ = lean_ctor_get(v_x_203_, 1);
v_v_205_ = lean_ctor_get(v_x_203_, 2);
v_l_206_ = lean_ctor_get(v_x_203_, 3);
v_r_207_ = lean_ctor_get(v_x_203_, 4);
v___x_208_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1_spec__1(v_init_202_, v_l_206_);
lean_inc(v_v_205_);
lean_inc(v_k_204_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v_k_204_);
lean_ctor_set(v___x_209_, 1, v_v_205_);
v___x_210_ = lean_array_push(v___x_208_, v___x_209_);
v_init_202_ = v___x_210_;
v_x_203_ = v_r_207_;
goto _start;
}
else
{
return v_init_202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_init_212_, lean_object* v_x_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1_spec__1(v_init_212_, v_x_213_);
lean_dec(v_x_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0(lean_object* v_env_215_, lean_object* v_as_216_, size_t v_i_217_, size_t v_stop_218_, lean_object* v_b_219_){
_start:
{
lean_object* v___y_221_; uint8_t v___x_225_; 
v___x_225_ = lean_usize_dec_eq(v_i_217_, v_stop_218_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v_fst_227_; uint8_t v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_226_ = lean_array_uget_borrowed(v_as_216_, v_i_217_);
v_fst_227_ = lean_ctor_get(v___x_226_, 0);
v___x_228_ = 1;
lean_inc_ref(v_env_215_);
v___x_229_ = l_Lean_Environment_setExporting(v_env_215_, v___x_228_);
lean_inc(v_fst_227_);
v___x_230_ = l_Lean_Environment_contains(v___x_229_, v_fst_227_, v___x_225_);
if (v___x_230_ == 0)
{
v___y_221_ = v_b_219_;
goto v___jp_220_;
}
else
{
lean_object* v___x_231_; 
lean_inc(v___x_226_);
v___x_231_ = lean_array_push(v_b_219_, v___x_226_);
v___y_221_ = v___x_231_;
goto v___jp_220_;
}
}
else
{
lean_dec_ref(v_env_215_);
return v_b_219_;
}
v___jp_220_:
{
size_t v___x_222_; size_t v___x_223_; 
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_add(v_i_217_, v___x_222_);
v_i_217_ = v___x_223_;
v_b_219_ = v___y_221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_232_, lean_object* v_as_233_, lean_object* v_i_234_, lean_object* v_stop_235_, lean_object* v_b_236_){
_start:
{
size_t v_i_boxed_237_; size_t v_stop_boxed_238_; lean_object* v_res_239_; 
v_i_boxed_237_ = lean_unbox_usize(v_i_234_);
lean_dec(v_i_234_);
v_stop_boxed_238_ = lean_unbox_usize(v_stop_235_);
lean_dec(v_stop_235_);
v_res_239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0(v_env_232_, v_as_233_, v_i_boxed_237_, v_stop_boxed_238_, v_b_236_);
lean_dec_ref(v_as_233_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_(lean_object* v___x_240_, lean_object* v_env_241_, lean_object* v_s_242_){
_start:
{
lean_object* v___y_244_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_253_ = lean_mk_empty_array_with_capacity(v___x_240_);
v___x_254_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1_spec__1(v___x_253_, v_s_242_);
v___x_255_ = lean_array_get_size(v___x_254_);
v___x_256_ = lean_mk_empty_array_with_capacity(v___x_240_);
v___x_257_ = lean_nat_dec_lt(v___x_240_, v___x_255_);
if (v___x_257_ == 0)
{
lean_dec_ref(v___x_254_);
v___y_244_ = v___x_256_;
goto v___jp_243_;
}
else
{
size_t v___x_258_; size_t v___x_259_; lean_object* v___x_260_; 
v___x_258_ = ((size_t)0ULL);
v___x_259_ = lean_usize_of_nat(v___x_255_);
lean_inc_ref(v_env_241_);
v___x_260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__2(v_env_241_, v___x_254_, v___x_258_, v___x_259_, v___x_256_);
lean_dec_ref(v___x_254_);
v___y_244_ = v___x_260_;
goto v___jp_243_;
}
v___jp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_245_ = lean_array_get_size(v___y_244_);
v___x_246_ = lean_mk_empty_array_with_capacity(v___x_240_);
v___x_247_ = lean_nat_dec_lt(v___x_240_, v___x_245_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
lean_dec_ref(v_env_241_);
lean_inc_ref(v___x_246_);
v___x_248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_246_);
lean_ctor_set(v___x_248_, 2, v___y_244_);
return v___x_248_;
}
else
{
size_t v___x_249_; size_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_249_ = ((size_t)0ULL);
v___x_250_ = lean_usize_of_nat(v___x_245_);
v___x_251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0(v_env_241_, v___y_244_, v___x_249_, v___x_250_, v___x_246_);
lean_inc_ref(v___x_251_);
v___x_252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_ctor_set(v___x_252_, 2, v___y_244_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2____boxed(lean_object* v___x_261_, lean_object* v_env_262_, lean_object* v_s_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_(v___x_261_, v_env_262_, v_s_263_);
lean_dec(v_s_263_);
lean_dec(v___x_261_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; 
v___f_272_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_));
v___x_273_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_));
v___x_274_ = lean_box(0);
v___x_275_ = 0;
v___x_276_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_273_, v___x_274_, v___x_275_, v___f_272_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2____boxed(lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_();
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1(lean_object* v_init_279_, lean_object* v_t_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1_spec__1(v_init_279_, v_t_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1___boxed(lean_object* v_init_282_, lean_object* v_t_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1(v_init_282_, v_t_283_);
lean_dec(v_t_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType(lean_object* v_type_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___x_296_; 
lean_inc_ref(v_type_290_);
v___x_296_ = l_Lean_Meta_isProp(v_type_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; uint8_t v___x_298_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v___x_298_ = lean_unbox(v_a_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
lean_dec_ref_known(v___x_296_, 1);
lean_inc_ref(v_type_290_);
v___x_299_ = l_Lean_Meta_isTypeFormerType(v_type_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; uint8_t v___x_301_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v___x_301_ = lean_unbox(v_a_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
lean_inc(v_a_300_);
lean_dec_ref_known(v___x_299_, 1);
v___x_302_ = l_Lean_Meta_whnfD(v_type_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_394_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_394_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_394_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_394_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
if (lean_obj_tag(v_a_303_) == 11)
{
lean_object* v_typeName_307_; 
v_typeName_307_ = lean_ctor_get(v_a_303_, 0);
lean_inc(v_typeName_307_);
if (lean_obj_tag(v_typeName_307_) == 1)
{
lean_object* v_pre_308_; 
v_pre_308_ = lean_ctor_get(v_typeName_307_, 0);
if (lean_obj_tag(v_pre_308_) == 0)
{
lean_object* v_idx_309_; lean_object* v_struct_310_; lean_object* v_str_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_idx_309_ = lean_ctor_get(v_a_303_, 1);
lean_inc(v_idx_309_);
v_struct_310_ = lean_ctor_get(v_a_303_, 2);
lean_inc_ref(v_struct_310_);
lean_dec_ref_known(v_a_303_, 3);
v_str_311_ = lean_ctor_get(v_typeName_307_, 1);
lean_inc_ref(v_str_311_);
lean_dec_ref_known(v_typeName_307_, 2);
v___x_312_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__0));
v___x_313_ = lean_string_dec_eq(v_str_311_, v___x_312_);
lean_dec_ref(v_str_311_);
if (v___x_313_ == 0)
{
lean_object* v___x_315_; 
lean_dec_ref(v_struct_310_);
lean_dec(v_idx_309_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_a_300_);
v___x_315_ = v___x_305_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_300_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = lean_nat_dec_eq(v_idx_309_, v___x_317_);
lean_dec(v_idx_309_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_321_; 
lean_dec_ref(v_struct_310_);
lean_dec(v_a_300_);
v___x_319_ = lean_box(v___x_318_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_319_);
v___x_321_ = v___x_305_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
else
{
if (lean_obj_tag(v_struct_310_) == 5)
{
lean_object* v_fn_323_; 
v_fn_323_ = lean_ctor_get(v_struct_310_, 0);
lean_inc_ref(v_fn_323_);
lean_dec_ref_known(v_struct_310_, 2);
if (lean_obj_tag(v_fn_323_) == 4)
{
lean_object* v_declName_324_; 
v_declName_324_ = lean_ctor_get(v_fn_323_, 0);
lean_inc(v_declName_324_);
if (lean_obj_tag(v_declName_324_) == 1)
{
lean_object* v_pre_325_; 
v_pre_325_ = lean_ctor_get(v_declName_324_, 0);
lean_inc(v_pre_325_);
if (lean_obj_tag(v_pre_325_) == 1)
{
lean_object* v_pre_326_; 
v_pre_326_ = lean_ctor_get(v_pre_325_, 0);
lean_inc(v_pre_326_);
if (lean_obj_tag(v_pre_326_) == 1)
{
lean_object* v_pre_327_; 
v_pre_327_ = lean_ctor_get(v_pre_326_, 0);
lean_inc(v_pre_327_);
if (lean_obj_tag(v_pre_327_) == 1)
{
lean_object* v_pre_328_; 
v_pre_328_ = lean_ctor_get(v_pre_327_, 0);
if (lean_obj_tag(v_pre_328_) == 0)
{
lean_object* v_us_329_; lean_object* v_str_330_; lean_object* v_str_331_; lean_object* v_str_332_; lean_object* v_str_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_us_329_ = lean_ctor_get(v_fn_323_, 1);
lean_inc(v_us_329_);
lean_dec_ref_known(v_fn_323_, 2);
v_str_330_ = lean_ctor_get(v_declName_324_, 1);
lean_inc_ref(v_str_330_);
lean_dec_ref_known(v_declName_324_, 2);
v_str_331_ = lean_ctor_get(v_pre_325_, 1);
lean_inc_ref(v_str_331_);
lean_dec_ref_known(v_pre_325_, 2);
v_str_332_ = lean_ctor_get(v_pre_326_, 1);
lean_inc_ref(v_str_332_);
lean_dec_ref_known(v_pre_326_, 2);
v_str_333_ = lean_ctor_get(v_pre_327_, 1);
lean_inc_ref(v_str_333_);
lean_dec_ref_known(v_pre_327_, 2);
v___x_334_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__1));
v___x_335_ = lean_string_dec_eq(v_str_333_, v___x_334_);
lean_dec_ref(v_str_333_);
if (v___x_335_ == 0)
{
lean_object* v___x_337_; 
lean_dec_ref(v_str_332_);
lean_dec_ref(v_str_331_);
lean_dec_ref(v_str_330_);
lean_dec(v_us_329_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_a_300_);
v___x_337_ = v___x_305_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_300_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
else
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__2));
v___x_340_ = lean_string_dec_eq(v_str_332_, v___x_339_);
lean_dec_ref(v_str_332_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_343_; 
lean_dec_ref(v_str_331_);
lean_dec_ref(v_str_330_);
lean_dec(v_us_329_);
lean_dec(v_a_300_);
v___x_341_ = lean_box(v___x_340_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_341_);
v___x_343_ = v___x_305_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
else
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__3));
v___x_346_ = lean_string_dec_eq(v_str_331_, v___x_345_);
lean_dec_ref(v_str_331_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_349_; 
lean_dec_ref(v_str_330_);
lean_dec(v_us_329_);
lean_dec(v_a_300_);
v___x_347_ = lean_box(v___x_346_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_347_);
v___x_349_ = v___x_305_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
else
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__4));
v___x_352_ = lean_string_dec_eq(v_str_330_, v___x_351_);
lean_dec_ref(v_str_330_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_355_; 
lean_dec(v_us_329_);
lean_dec(v_a_300_);
v___x_353_ = lean_box(v___x_352_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_353_);
v___x_355_ = v___x_305_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
else
{
if (lean_obj_tag(v_us_329_) == 0)
{
lean_object* v___x_357_; lean_object* v___x_359_; 
lean_dec(v_a_300_);
v___x_357_ = lean_box(v___x_352_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_357_);
v___x_359_ = v___x_305_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
else
{
lean_object* v___x_362_; 
lean_dec(v_us_329_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_a_300_);
v___x_362_ = v___x_305_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_300_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_365_; 
lean_dec_ref_known(v_pre_327_, 2);
lean_dec_ref_known(v_pre_326_, 2);
lean_dec_ref_known(v_pre_325_, 2);
lean_dec_ref_known(v_declName_324_, 2);
lean_dec_ref_known(v_fn_323_, 2);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_a_300_);
v___x_365_ = v___x_305_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_300_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
else
{
lean_object* v___x_368_; 
lean_dec_ref_known(v_pre_326_, 2);
lean_dec(v_pre_327_);
lean_dec_ref_known(v_pre_325_, 2);
lean_dec_ref_known(v_declName_324_, 2);
lean_dec_ref_known(v_fn_323_, 2);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_a_300_);
v___x_368_ = v___x_305_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_300_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v___x_371_; 
lean_dec(v_pre_326_);
lean_dec_ref_known(v_pre_325_, 2);
lean_dec_ref_known(v_declName_324_, 2);
lean_dec_ref_known(v_fn_323_, 2);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_a_300_);
v___x_371_ = v___x_305_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_300_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v___x_374_; 
lean_dec_ref_known(v_declName_324_, 2);
lean_dec(v_pre_325_);
lean_dec_ref_known(v_fn_323_, 2);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_a_300_);
v___x_374_ = v___x_305_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_300_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
else
{
lean_object* v___x_377_; 
lean_dec_ref_known(v_fn_323_, 2);
lean_dec(v_declName_324_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_a_300_);
v___x_377_ = v___x_305_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_300_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
lean_object* v___x_380_; 
lean_dec_ref(v_fn_323_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_a_300_);
v___x_380_ = v___x_305_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_300_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
else
{
lean_object* v___x_383_; 
lean_dec_ref(v_struct_310_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_a_300_);
v___x_383_ = v___x_305_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_300_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
}
else
{
lean_object* v___x_386_; 
lean_dec_ref_known(v_typeName_307_, 2);
lean_dec_ref_known(v_a_303_, 3);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_a_300_);
v___x_386_ = v___x_305_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_300_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
else
{
lean_object* v___x_389_; 
lean_dec(v_typeName_307_);
lean_dec_ref_known(v_a_303_, 3);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_a_300_);
v___x_389_ = v___x_305_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_300_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
lean_object* v___x_392_; 
lean_dec(v_a_303_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_a_300_);
v___x_392_ = v___x_305_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_300_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec(v_a_300_);
v_a_395_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_302_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_302_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
lean_dec_ref(v_type_290_);
return v___x_299_;
}
}
else
{
lean_dec_ref(v_type_290_);
return v___x_299_;
}
}
else
{
lean_dec_ref(v_type_290_);
return v___x_296_;
}
}
else
{
lean_dec_ref(v_type_290_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___boxed(lean_object* v_type_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType(v_type_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f(lean_object* v_declName_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt;
v___x_416_ = ((lean_object*)(l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f___closed__0));
v___x_417_ = l_Lean_Compiler_LCNF_Irrelevant_setHasTrivialStructure_x3f(v___x_415_, v___x_416_, v_declName_411_, v_a_412_, v_a_413_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f___boxed(lean_object* v_declName_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f(v_declName_418_, v_a_419_, v_a_420_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(lean_object* v_declName_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt;
v___x_428_ = l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(v___x_427_, v_declName_423_, v_a_424_, v_a_425_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___boxed(lean_object* v_declName_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_declName_429_, v_a_430_, v_a_431_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
return v_res_433_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_box(0);
v___x_444_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__7));
v___x_445_ = l_Lean_Expr_const___override(v___x_444_, v___x_443_);
return v___x_445_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8);
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_box(0);
v___x_452_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__11));
v___x_453_ = l_Lean_Expr_const___override(v___x_452_, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_box(0);
v___x_459_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__14));
v___x_460_ = l_Lean_Expr_const___override(v___x_459_, v___x_458_);
return v___x_460_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15);
v___x_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_box(0);
v___x_466_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__17));
v___x_467_ = l_Lean_Expr_const___override(v___x_466_, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18);
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_box(0);
v___x_473_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__20));
v___x_474_ = l_Lean_Expr_const___override(v___x_473_, v___x_472_);
return v___x_474_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_box(0);
v___x_480_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__23));
v___x_481_ = l_Lean_Expr_const___override(v___x_480_, v___x_479_);
return v___x_481_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_box(0);
v___x_487_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__26));
v___x_488_ = l_Lean_Expr_const___override(v___x_487_, v___x_486_);
return v___x_488_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5);
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8);
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11);
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(lean_object* v_x_497_){
_start:
{
if (lean_obj_tag(v_x_497_) == 1)
{
lean_object* v_pre_498_; 
v_pre_498_ = lean_ctor_get(v_x_497_, 0);
if (lean_obj_tag(v_pre_498_) == 0)
{
lean_object* v_str_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_str_499_ = lean_ctor_get(v_x_497_, 1);
v___x_500_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9));
v___x_501_ = lean_string_dec_eq(v_str_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6));
v___x_503_ = lean_string_dec_eq(v_str_499_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3));
v___x_505_ = lean_string_dec_eq(v_str_499_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__0));
v___x_507_ = lean_string_dec_eq(v_str_499_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__1));
v___x_509_ = lean_string_dec_eq(v_str_499_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__2));
v___x_511_ = lean_string_dec_eq(v_str_499_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__3));
v___x_513_ = lean_string_dec_eq(v_str_499_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__4));
v___x_515_ = lean_string_dec_eq(v_str_499_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__5));
v___x_517_ = lean_string_dec_eq(v_str_499_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__6));
v___x_519_ = lean_string_dec_eq(v_str_499_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
v___x_520_ = lean_box(0);
return v___x_520_;
}
else
{
lean_object* v___x_521_; 
v___x_521_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9);
return v___x_521_;
}
}
else
{
lean_object* v___x_522_; 
v___x_522_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13);
return v___x_522_;
}
}
else
{
lean_object* v___x_523_; 
v___x_523_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16);
return v___x_523_;
}
}
else
{
lean_object* v___x_524_; 
v___x_524_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19);
return v___x_524_;
}
}
else
{
lean_object* v___x_525_; 
v___x_525_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22);
return v___x_525_;
}
}
else
{
lean_object* v___x_526_; 
v___x_526_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25);
return v___x_526_;
}
}
else
{
lean_object* v___x_527_; 
v___x_527_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28);
return v___x_527_;
}
}
else
{
lean_object* v___x_528_; 
v___x_528_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29);
return v___x_528_;
}
}
else
{
lean_object* v___x_529_; 
v___x_529_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30);
return v___x_529_;
}
}
else
{
lean_object* v___x_530_; 
v___x_530_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31);
return v___x_530_;
}
}
else
{
lean_object* v___x_531_; 
v___x_531_ = lean_box(0);
return v___x_531_;
}
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_box(0);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___boxed(lean_object* v_x_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(v_x_533_);
lean_dec(v_x_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(lean_object* v_msg_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___f_540_; lean_object* v___x_5619__overap_541_; lean_object* v___x_542_; 
v___f_540_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0));
v___x_5619__overap_541_ = lean_panic_fn_borrowed(v___f_540_, v_msg_536_);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
v___x_542_ = lean_apply_3(v___x_5619__overap_541_, v___y_537_, v___y_538_, lean_box(0));
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___boxed(lean_object* v_msg_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(v_msg_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0(lean_object* v_k_548_, lean_object* v_b_549_, lean_object* v_c_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; 
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
v___x_556_ = lean_apply_7(v_k_548_, v_b_549_, v_c_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, lean_box(0));
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0___boxed(lean_object* v_k_557_, lean_object* v_b_558_, lean_object* v_c_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0(v_k_557_, v_b_558_, v_c_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(lean_object* v_type_566_, lean_object* v_k_567_, uint8_t v_cleanupAnnotations_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___f_574_; uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___f_574_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_574_, 0, v_k_567_);
v___x_575_ = 0;
v___x_576_ = lean_box(0);
v___x_577_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_575_, v___x_576_, v_type_566_, v___f_574_, v_cleanupAnnotations_568_, v___x_575_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_a_586_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_577_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_577_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___boxed(lean_object* v_type_594_, lean_object* v_k_595_, lean_object* v_cleanupAnnotations_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_602_; lean_object* v_res_603_; 
v_cleanupAnnotations_boxed_602_ = lean_unbox(v_cleanupAnnotations_596_);
v_res_603_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(v_type_594_, v_k_595_, v_cleanupAnnotations_boxed_602_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3(lean_object* v_00_u03b1_604_, lean_object* v_type_605_, lean_object* v_k_606_, uint8_t v_cleanupAnnotations_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(v_type_605_, v_k_606_, v_cleanupAnnotations_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___boxed(lean_object* v_00_u03b1_614_, lean_object* v_type_615_, lean_object* v_k_616_, lean_object* v_cleanupAnnotations_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_623_; lean_object* v_res_624_; 
v_cleanupAnnotations_boxed_623_ = lean_unbox(v_cleanupAnnotations_617_);
v_res_624_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3(v_00_u03b1_614_, v_type_615_, v_k_616_, v_cleanupAnnotations_boxed_623_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_624_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_625_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg(){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__1);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___boxed(lean_object* v___dummy_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg();
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(lean_object* v_a_635_, lean_object* v_b_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_array_642_; lean_object* v_start_643_; lean_object* v_stop_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_701_; 
v_array_642_ = lean_ctor_get(v_a_635_, 0);
v_start_643_ = lean_ctor_get(v_a_635_, 1);
v_stop_644_ = lean_ctor_get(v_a_635_, 2);
v_isSharedCheck_701_ = !lean_is_exclusive(v_a_635_);
if (v_isSharedCheck_701_ == 0)
{
v___x_646_ = v_a_635_;
v_isShared_647_ = v_isSharedCheck_701_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_stop_644_);
lean_inc(v_start_643_);
lean_inc(v_array_642_);
lean_dec(v_a_635_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_701_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
uint8_t v___x_648_; 
v___x_648_ = lean_nat_dec_lt(v_start_643_, v_stop_644_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
lean_del_object(v___x_646_);
lean_dec(v_stop_644_);
lean_dec(v_start_643_);
lean_dec_ref(v_array_642_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v_b_636_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
lean_dec_ref(v_b_636_);
v___x_650_ = lean_box(0);
v___x_651_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___closed__0));
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_nat_add(v_start_643_, v___x_652_);
lean_inc_ref(v_array_642_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 1, v___x_653_);
v___x_655_ = v___x_646_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_array_642_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_stop_644_);
v___x_655_ = v_reuseFailAlloc_700_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_array_fget(v_array_642_, v_start_643_);
lean_dec(v_start_643_);
lean_dec_ref(v_array_642_);
v___x_657_ = l_Lean_Expr_fvarId_x21(v___x_656_);
lean_dec(v___x_656_);
v___x_658_ = l_Lean_FVarId_getType___redArg(v___x_657_, v___y_637_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_660_ = l_Lean_Compiler_LCNF_toLCNFType(v_a_659_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_662_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_660_, 1);
v___x_662_ = l_Lean_Compiler_LCNF_toMonoType(v_a_661_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_675_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_675_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_675_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_675_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
uint8_t v___x_667_; 
v___x_667_ = l_Lean_Expr_isErased(v_a_663_);
lean_dec(v_a_663_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
lean_dec_ref(v___x_655_);
v___x_668_ = lean_box(v___x_648_);
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v___x_650_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_670_);
v___x_672_ = v___x_665_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
else
{
lean_del_object(v___x_665_);
v_a_635_ = v___x_655_;
v_b_636_ = v___x_651_;
goto _start;
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v___x_655_);
v_a_676_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_662_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_662_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref(v___x_655_);
v_a_684_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_660_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_660_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec_ref(v___x_655_);
v_a_692_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_658_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_658_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___boxed(lean_object* v_a_702_, lean_object* v_b_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(v_a_702_, v_b_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___lam__0(uint8_t v___x_710_, lean_object* v_numParams_711_, lean_object* v___x_712_, lean_object* v_params_713_, lean_object* v_x_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_lower_721_; lean_object* v_upper_722_; lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_array_get_size(v_params_713_);
v___x_749_ = lean_nat_dec_le(v_numParams_711_, v___x_712_);
if (v___x_749_ == 0)
{
lean_dec(v___x_712_);
v_lower_721_ = v_numParams_711_;
v_upper_722_ = v___x_748_;
goto v___jp_720_;
}
else
{
lean_dec(v_numParams_711_);
v_lower_721_ = v___x_712_;
v_upper_722_ = v___x_748_;
goto v___jp_720_;
}
v___jp_720_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_723_ = l_Array_toSubarray___redArg(v_params_713_, v_lower_721_, v_upper_722_);
v___x_724_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___closed__0));
v___x_725_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(v___x_723_, v___x_724_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_739_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_739_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_739_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_739_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_fst_730_; 
v_fst_730_ = lean_ctor_get(v_a_726_, 0);
lean_inc(v_fst_730_);
lean_dec(v_a_726_);
if (lean_obj_tag(v_fst_730_) == 0)
{
lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_731_ = lean_box(v___x_710_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_731_);
v___x_733_ = v___x_728_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
else
{
lean_object* v_val_735_; lean_object* v___x_737_; 
v_val_735_ = lean_ctor_get(v_fst_730_, 0);
lean_inc(v_val_735_);
lean_dec_ref_known(v_fst_730_, 1);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v_val_735_);
v___x_737_ = v___x_728_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_val_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
v_a_740_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_725_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_725_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___lam__0___boxed(lean_object* v___x_750_, lean_object* v_numParams_751_, lean_object* v___x_752_, lean_object* v_params_753_, lean_object* v_x_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
uint8_t v___x_7103__boxed_760_; lean_object* v_res_761_; 
v___x_7103__boxed_760_ = lean_unbox(v___x_750_);
v_res_761_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___lam__0(v___x_7103__boxed_760_, v_numParams_751_, v___x_752_, v_params_753_, v_x_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec_ref(v_x_754_);
return v_res_761_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_765_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__2));
v___x_766_ = lean_unsigned_to_nat(58u);
v___x_767_ = lean_unsigned_to_nat(93u);
v___x_768_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__1));
v___x_769_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__0));
v___x_770_ = l_mkPanicMessageWithDecl(v___x_769_, v___x_768_, v___x_767_, v___x_766_, v___x_765_);
return v___x_770_;
}
}
static uint64_t _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_777_; uint64_t v___x_778_; 
v___x_777_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__4));
v___x_778_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__6(void){
_start:
{
uint64_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = lean_uint64_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__5);
v___x_780_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__4));
v___x_781_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set_uint64(v___x_781_, sizeof(void*)*1, v___x_779_);
return v___x_781_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__8(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_784_ = lean_unsigned_to_nat(32u);
v___x_785_ = lean_mk_empty_array_with_capacity(v___x_784_);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__9(void){
_start:
{
size_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_787_ = ((size_t)5ULL);
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = lean_unsigned_to_nat(32u);
v___x_790_ = lean_mk_empty_array_with_capacity(v___x_789_);
v___x_791_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__8);
v___x_792_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v___x_790_);
lean_ctor_set(v___x_792_, 2, v___x_788_);
lean_ctor_set(v___x_792_, 3, v___x_788_);
lean_ctor_set_usize(v___x_792_, 4, v___x_787_);
return v___x_792_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__10(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_793_ = lean_box(1);
v___x_794_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__9);
v___x_795_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7);
v___x_796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v___x_794_);
lean_ctor_set(v___x_796_, 2, v___x_793_);
return v___x_796_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__12(void){
_start:
{
uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_799_ = 1;
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_box(0);
v___x_802_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__11));
v___x_803_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__10);
v___x_804_ = lean_box(1);
v___x_805_ = 0;
v___x_806_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__6);
v___x_807_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v___x_804_);
lean_ctor_set(v___x_807_, 2, v___x_803_);
lean_ctor_set(v___x_807_, 3, v___x_802_);
lean_ctor_set(v___x_807_, 4, v___x_801_);
lean_ctor_set(v___x_807_, 5, v___x_800_);
lean_ctor_set(v___x_807_, 6, v___x_801_);
lean_ctor_set_uint8(v___x_807_, sizeof(void*)*7, v___x_805_);
lean_ctor_set_uint8(v___x_807_, sizeof(void*)*7 + 1, v___x_805_);
lean_ctor_set_uint8(v___x_807_, sizeof(void*)*7 + 2, v___x_805_);
lean_ctor_set_uint8(v___x_807_, sizeof(void*)*7 + 3, v___x_799_);
return v___x_807_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7);
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
lean_ctor_set(v___x_810_, 2, v___x_809_);
lean_ctor_set(v___x_810_, 3, v___x_809_);
lean_ctor_set(v___x_810_, 4, v___x_808_);
lean_ctor_set(v___x_810_, 5, v___x_808_);
lean_ctor_set(v___x_810_, 6, v___x_808_);
lean_ctor_set(v___x_810_, 7, v___x_808_);
lean_ctor_set(v___x_810_, 8, v___x_808_);
lean_ctor_set(v___x_810_, 9, v___x_808_);
lean_ctor_set(v___x_810_, 10, v___x_808_);
return v___x_810_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14(void){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg();
return v___x_811_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
return v___x_813_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__16(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7);
v___x_816_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
lean_ctor_set(v___x_816_, 2, v___x_814_);
return v___x_816_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_817_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__16, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__16_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__16);
v___x_818_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__15, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__15_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__15);
v___x_819_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7);
v___x_820_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14);
v___x_821_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v___x_819_);
lean_ctor_set(v___x_821_, 2, v___x_818_);
lean_ctor_set(v___x_821_, 3, v___x_819_);
lean_ctor_set(v___x_821_, 4, v___x_819_);
lean_ctor_set(v___x_821_, 5, v___x_819_);
lean_ctor_set(v___x_821_, 6, v___x_819_);
lean_ctor_set(v___x_821_, 7, v___x_817_);
return v___x_821_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__18(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__7);
v___x_823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
lean_ctor_set(v___x_823_, 2, v___x_822_);
lean_ctor_set(v___x_823_, 3, v___x_822_);
lean_ctor_set(v___x_823_, 4, v___x_822_);
return v___x_823_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_824_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__18, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__18_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__18);
v___x_825_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__9);
v___x_826_ = lean_box(1);
v___x_827_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__17, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__17_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__17);
v___x_828_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__13, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__13_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__13);
v___x_829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v___x_827_);
lean_ctor_set(v___x_829_, 2, v___x_826_);
lean_ctor_set(v___x_829_, 3, v___x_825_);
lean_ctor_set(v___x_829_, 4, v___x_824_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg(lean_object* v___x_830_, lean_object* v_as_x27_831_, lean_object* v_b_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
if (lean_obj_tag(v_as_x27_831_) == 0)
{
lean_object* v___x_836_; 
lean_dec_ref(v___x_830_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v_b_832_);
return v___x_836_;
}
else
{
lean_object* v_head_837_; lean_object* v_tail_838_; lean_object* v___y_840_; lean_object* v___y_841_; uint8_t v___x_853_; lean_object* v___x_854_; 
v_head_837_ = lean_ctor_get(v_as_x27_831_, 0);
v_tail_838_ = lean_ctor_get(v_as_x27_831_, 1);
v___x_853_ = 0;
lean_inc(v_head_837_);
lean_inc_ref(v___x_830_);
v___x_854_ = l_Lean_Environment_find_x3f(v___x_830_, v_head_837_, v___x_853_);
if (lean_obj_tag(v___x_854_) == 1)
{
lean_object* v_val_855_; 
v_val_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_val_855_);
lean_dec_ref_known(v___x_854_, 1);
if (lean_obj_tag(v_val_855_) == 6)
{
lean_object* v_val_856_; lean_object* v_toConstantVal_857_; lean_object* v_numParams_858_; lean_object* v_type_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___f_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_val_856_ = lean_ctor_get(v_val_855_, 0);
lean_inc_ref(v_val_856_);
lean_dec_ref_known(v_val_855_, 1);
v_toConstantVal_857_ = lean_ctor_get(v_val_856_, 0);
lean_inc_ref(v_toConstantVal_857_);
v_numParams_858_ = lean_ctor_get(v_val_856_, 3);
lean_inc(v_numParams_858_);
lean_dec_ref(v_val_856_);
v_type_859_ = lean_ctor_get(v_toConstantVal_857_, 2);
lean_inc_ref(v_type_859_);
lean_dec_ref(v_toConstantVal_857_);
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_box(v___x_853_);
v___f_862_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_862_, 0, v___x_861_);
lean_closure_set(v___f_862_, 1, v_numParams_858_);
lean_closure_set(v___f_862_, 2, v___x_860_);
v___x_863_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__12);
v___x_864_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__19, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__19_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__19);
v___x_865_ = lean_st_mk_ref(v___x_864_);
v___x_866_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(v_type_859_, v___f_862_, v___x_853_, v___x_863_, v___x_865_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
v___x_868_ = lean_st_ref_get(v___x_865_);
lean_dec(v___x_865_);
lean_dec(v___x_868_);
v___x_869_ = lean_unbox(v_a_867_);
lean_dec(v_a_867_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_unsigned_to_nat(1u);
v___x_871_ = lean_nat_add(v_b_832_, v___x_870_);
lean_dec(v_b_832_);
v_as_x27_831_ = v_tail_838_;
v_b_832_ = v___x_871_;
goto _start;
}
else
{
v_as_x27_831_ = v_tail_838_;
goto _start;
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec(v___x_865_);
lean_dec(v_b_832_);
lean_dec_ref(v___x_830_);
v_a_874_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_866_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_866_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_dec(v_val_855_);
v___y_840_ = v___y_833_;
v___y_841_ = v___y_834_;
goto v___jp_839_;
}
}
else
{
lean_dec(v___x_854_);
v___y_840_ = v___y_833_;
v___y_841_ = v___y_834_;
goto v___jp_839_;
}
v___jp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__3);
v___x_843_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(v___x_842_, v___y_840_, v___y_841_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_dec_ref_known(v___x_843_, 1);
v_as_x27_831_ = v_tail_838_;
goto _start;
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec(v_b_832_);
lean_dec_ref(v___x_830_);
v_a_845_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_843_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_843_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___boxed(lean_object* v___x_882_, lean_object* v_as_x27_883_, lean_object* v_b_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg(v___x_882_, v_as_x27_883_, v_b_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v_as_x27_883_);
return v_res_888_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_box(0);
v___x_893_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__1));
v___x_894_ = l_Lean_Expr_const___override(v___x_893_, v___x_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType(lean_object* v_name_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(v_name_895_);
if (lean_obj_tag(v___x_902_) == 1)
{
lean_object* v_val_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_name_895_);
v_val_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_val_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set_tag(v___x_905_, 0);
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_val_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
else
{
lean_object* v___x_911_; lean_object* v_env_912_; uint8_t v___x_913_; lean_object* v___x_914_; 
lean_dec(v___x_902_);
v___x_911_ = lean_st_ref_get(v_a_897_);
v_env_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc_ref_n(v_env_912_, 2);
lean_dec(v___x_911_);
v___x_913_ = 0;
v___x_914_ = l_Lean_Environment_find_x3f(v_env_912_, v_name_895_, v___x_913_);
if (lean_obj_tag(v___x_914_) == 1)
{
lean_object* v_val_915_; 
v_val_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_val_915_);
lean_dec_ref_known(v___x_914_, 1);
if (lean_obj_tag(v_val_915_) == 5)
{
lean_object* v_val_916_; lean_object* v_ctors_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_val_916_ = lean_ctor_get(v_val_915_, 0);
lean_inc_ref(v_val_916_);
lean_dec_ref_known(v_val_915_, 1);
v_ctors_917_ = lean_ctor_get(v_val_916_, 4);
lean_inc(v_ctors_917_);
lean_dec_ref(v_val_916_);
v___x_918_ = l_List_lengthTR___redArg(v_ctors_917_);
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_920_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg(v_env_912_, v_ctors_917_, v___x_919_, v_a_896_, v_a_897_);
lean_dec(v_ctors_917_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_939_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_939_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_939_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_939_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
uint8_t v___x_925_; 
v___x_925_ = lean_nat_dec_eq(v_a_921_, v___x_918_);
if (v___x_925_ == 0)
{
uint8_t v___x_926_; 
lean_dec(v___x_918_);
v___x_926_ = lean_nat_dec_eq(v_a_921_, v___x_919_);
lean_dec(v_a_921_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_927_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_927_);
v___x_929_ = v___x_923_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_931_);
v___x_933_ = v___x_923_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_937_; 
lean_dec(v_a_921_);
v___x_935_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum(v___x_918_);
lean_dec(v___x_918_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_935_);
v___x_937_ = v___x_923_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v___x_918_);
v_a_940_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_920_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_920_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_dec(v_val_915_);
lean_dec_ref(v_env_912_);
goto v___jp_899_;
}
}
else
{
lean_dec(v___x_914_);
lean_dec_ref(v_env_912_);
goto v___jp_899_;
}
}
v___jp_899_:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___boxed(lean_object* v_name_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType(v_name_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1(lean_object* v_inst_953_, lean_object* v_R_954_, lean_object* v_a_955_, lean_object* v_b_956_, lean_object* v_c_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(v_a_955_, v_b_956_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___boxed(lean_object* v_inst_964_, lean_object* v_R_965_, lean_object* v_a_966_, lean_object* v_b_967_, lean_object* v_c_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1(v_inst_964_, v_R_965_, v_a_966_, v_b_967_, v_c_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2(lean_object* v_00_u03b2_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg(){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___boxed(lean_object* v___dummy_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg();
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2(lean_object* v_00_u03b2_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__14);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4(lean_object* v___x_983_, lean_object* v_as_984_, lean_object* v_as_x27_985_, lean_object* v_b_986_, lean_object* v_a_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg(v___x_983_, v_as_x27_985_, v_b_986_, v___y_988_, v___y_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___boxed(lean_object* v___x_992_, lean_object* v_as_993_, lean_object* v_as_x27_994_, lean_object* v_b_995_, lean_object* v_a_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4(v___x_992_, v_as_993_, v_as_x27_994_, v_b_995_, v_a_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v_as_x27_994_);
lean_dec(v_as_993_);
return v_res_1000_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setImpureType___closed__0(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0);
v___x_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setImpureType___closed__1(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_obj_once(&l_Lean_Compiler_LCNF_setImpureType___closed__0, &l_Lean_Compiler_LCNF_setImpureType___closed__0_once, _init_l_Lean_Compiler_LCNF_setImpureType___closed__0);
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setImpureType(lean_object* v_name_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(v_name_1005_);
if (lean_obj_tag(v___x_1009_) == 0)
{
uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v_env_1012_; lean_object* v___x_1013_; lean_object* v_toEnvExtension_1014_; lean_object* v_asyncMode_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; 
v___x_1010_ = 0;
v___x_1011_ = lean_st_ref_get(v_a_1007_);
v_env_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc_ref(v_env_1012_);
lean_dec(v___x_1011_);
v___x_1013_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt;
v_toEnvExtension_1014_ = lean_ctor_get(v___x_1013_, 0);
v_asyncMode_1015_ = lean_ctor_get(v_toEnvExtension_1014_, 2);
v___x_1016_ = 0;
lean_inc(v_name_1005_);
v___x_1017_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1013_, v_env_1012_, v_name_1005_, v_asyncMode_1015_, v___x_1016_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v___x_1018_; 
lean_inc(v_name_1005_);
v___x_1018_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType(v_name_1005_, v_a_1006_, v_a_1007_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1048_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1048_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1048_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v_env_1024_; lean_object* v_nextMacroScope_1025_; lean_object* v_ngen_1026_; lean_object* v_auxDeclNGen_1027_; lean_object* v_traceState_1028_; lean_object* v_recordedDeps_1029_; lean_object* v_messages_1030_; lean_object* v_infoState_1031_; lean_object* v_snapshotTasks_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1046_; 
v___x_1023_ = lean_st_ref_take(v_a_1007_);
v_env_1024_ = lean_ctor_get(v___x_1023_, 0);
v_nextMacroScope_1025_ = lean_ctor_get(v___x_1023_, 1);
v_ngen_1026_ = lean_ctor_get(v___x_1023_, 2);
v_auxDeclNGen_1027_ = lean_ctor_get(v___x_1023_, 3);
v_traceState_1028_ = lean_ctor_get(v___x_1023_, 4);
v_recordedDeps_1029_ = lean_ctor_get(v___x_1023_, 6);
v_messages_1030_ = lean_ctor_get(v___x_1023_, 7);
v_infoState_1031_ = lean_ctor_get(v___x_1023_, 8);
v_snapshotTasks_1032_ = lean_ctor_get(v___x_1023_, 9);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v___x_1023_, 5);
lean_dec(v_unused_1047_);
v___x_1034_ = v___x_1023_;
v_isShared_1035_ = v_isSharedCheck_1046_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_snapshotTasks_1032_);
lean_inc(v_infoState_1031_);
lean_inc(v_messages_1030_);
lean_inc(v_recordedDeps_1029_);
lean_inc(v_traceState_1028_);
lean_inc(v_auxDeclNGen_1027_);
lean_inc(v_ngen_1026_);
lean_inc(v_nextMacroScope_1025_);
lean_inc(v_env_1024_);
lean_dec(v___x_1023_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1046_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1036_ = lean_box(0);
v___x_1037_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1013_, v_env_1024_, v_name_1005_, v_a_1019_, v___x_1010_);
v___x_1038_ = lean_obj_once(&l_Lean_Compiler_LCNF_setImpureType___closed__1, &l_Lean_Compiler_LCNF_setImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_setImpureType___closed__1);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 5, v___x_1038_);
lean_ctor_set(v___x_1034_, 0, v___x_1037_);
v___x_1040_ = v___x_1034_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_nextMacroScope_1025_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_ngen_1026_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_auxDeclNGen_1027_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_traceState_1028_);
lean_ctor_set(v_reuseFailAlloc_1045_, 5, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1045_, 6, v_recordedDeps_1029_);
lean_ctor_set(v_reuseFailAlloc_1045_, 7, v_messages_1030_);
lean_ctor_set(v_reuseFailAlloc_1045_, 8, v_infoState_1031_);
lean_ctor_set(v_reuseFailAlloc_1045_, 9, v_snapshotTasks_1032_);
v___x_1040_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1041_ = lean_st_ref_put(v_a_1007_, v___x_1040_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1036_);
v___x_1043_ = v___x_1021_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1036_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v_name_1005_);
v_a_1049_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1018_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1018_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v_name_1005_);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v___x_1017_, 0);
lean_dec(v_unused_1065_);
v___x_1058_ = v___x_1017_;
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
else
{
lean_dec(v___x_1017_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1060_ = lean_box(0);
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1060_);
v___x_1062_ = v___x_1058_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v_name_1005_);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; 
v_unused_1074_ = lean_ctor_get(v___x_1009_, 0);
lean_dec(v_unused_1074_);
v___x_1067_ = v___x_1009_;
v_isShared_1068_ = v_isSharedCheck_1073_;
goto v_resetjp_1066_;
}
else
{
lean_dec(v___x_1009_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1073_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1069_ = lean_box(0);
if (v_isShared_1068_ == 0)
{
lean_ctor_set_tag(v___x_1067_, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1069_);
v___x_1071_ = v___x_1067_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setImpureType___boxed(lean_object* v_name_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_Compiler_LCNF_setImpureType(v_name_1075_, v_a_1076_, v_a_1077_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
return v_res_1079_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2_spec__2___redArg___closed__0);
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0);
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
lean_ctor_set(v___x_1084_, 2, v___x_1083_);
lean_ctor_set(v___x_1084_, 3, v___x_1083_);
lean_ctor_set(v___x_1084_, 4, v___x_1082_);
lean_ctor_set(v___x_1084_, 5, v___x_1082_);
lean_ctor_set(v___x_1084_, 6, v___x_1082_);
lean_ctor_set(v___x_1084_, 7, v___x_1082_);
lean_ctor_set(v___x_1084_, 8, v___x_1082_);
lean_ctor_set(v___x_1084_, 9, v___x_1082_);
lean_ctor_set(v___x_1084_, 10, v___x_1082_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1085_ = lean_box(1);
v___x_1086_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__9);
v___x_1087_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0);
v___x_1088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v___x_1086_);
lean_ctor_set(v___x_1088_, 2, v___x_1085_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0(lean_object* v_msgData_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; lean_object* v_toCold_1094_; lean_object* v_env_1095_; lean_object* v_options_1096_; uint8_t v___x_1097_; lean_object* v_env_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1093_ = lean_st_ref_get(v___y_1091_);
v_toCold_1094_ = lean_ctor_get(v___y_1090_, 0);
v_env_1095_ = lean_ctor_get(v___x_1093_, 0);
lean_inc_ref(v_env_1095_);
lean_dec(v___x_1093_);
v_options_1096_ = lean_ctor_get(v_toCold_1094_, 2);
v___x_1097_ = 0;
v_env_1098_ = l_Lean_Environment_setRecordingDeps(v_env_1095_, v___x_1097_);
v___x_1099_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1);
v___x_1100_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2);
lean_inc_ref(v_options_1096_);
v___x_1101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1101_, 0, v_env_1098_);
lean_ctor_set(v___x_1101_, 1, v___x_1099_);
lean_ctor_set(v___x_1101_, 2, v___x_1100_);
lean_ctor_set(v___x_1101_, 3, v_options_1096_);
v___x_1102_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v_msgData_1089_);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___boxed(lean_object* v_msgData_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0(v_msgData_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(lean_object* v_msg_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_ref_1113_; lean_object* v___x_1114_; lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1123_; 
v_ref_1113_ = lean_ctor_get(v___y_1110_, 2);
v___x_1114_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0(v_msg_1109_, v___y_1110_, v___y_1111_);
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1123_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1123_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1121_; 
lean_inc(v_ref_1113_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v_ref_1113_);
lean_ctor_set(v___x_1119_, 1, v_a_1115_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 1);
lean_ctor_set(v___x_1117_, 0, v___x_1119_);
v___x_1121_ = v___x_1117_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___boxed(lean_object* v_msg_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_msg_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1128_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = ((lean_object*)(l_Lean_Compiler_LCNF_nameToImpureType___closed__0));
v___x_1131_ = l_Lean_stringToMessageData(v___x_1130_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__3(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = ((lean_object*)(l_Lean_Compiler_LCNF_nameToImpureType___closed__2));
v___x_1134_ = l_Lean_stringToMessageData(v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_nameToImpureType(lean_object* v_name_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(v_name_1135_);
if (lean_obj_tag(v___x_1142_) == 1)
{
lean_object* v_val_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v_name_1135_);
v_val_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_val_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 0);
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_val_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
lean_object* v___x_1151_; lean_object* v_env_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; 
lean_dec(v___x_1142_);
v___x_1151_ = lean_st_ref_get(v_a_1137_);
v_env_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc_ref(v_env_1152_);
lean_dec(v___x_1151_);
v___x_1153_ = 0;
lean_inc(v_name_1135_);
v___x_1154_ = l_Lean_Environment_find_x3f(v_env_1152_, v_name_1135_, v___x_1153_);
if (lean_obj_tag(v___x_1154_) == 1)
{
lean_object* v_val_1155_; 
v_val_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_val_1155_);
lean_dec_ref_known(v___x_1154_, 1);
if (lean_obj_tag(v_val_1155_) == 5)
{
lean_object* v___x_1156_; lean_object* v_env_1157_; lean_object* v___x_1158_; lean_object* v_toEnvExtension_1159_; lean_object* v_asyncMode_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; 
lean_dec_ref_known(v_val_1155_, 1);
v___x_1156_ = lean_st_ref_get(v_a_1137_);
v_env_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc_ref(v_env_1157_);
lean_dec(v___x_1156_);
v___x_1158_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt;
v_toEnvExtension_1159_ = lean_ctor_get(v___x_1158_, 0);
v_asyncMode_1160_ = lean_ctor_get(v_toEnvExtension_1159_, 2);
v___x_1161_ = 0;
lean_inc(v_name_1135_);
v___x_1162_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1158_, v_env_1157_, v_name_1135_, v_asyncMode_1160_, v___x_1161_);
if (lean_obj_tag(v___x_1162_) == 1)
{
lean_object* v_val_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec(v_name_1135_);
v_val_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_val_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set_tag(v___x_1165_, 0);
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_val_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec(v___x_1162_);
v___x_1171_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__1, &l_Lean_Compiler_LCNF_nameToImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1);
v___x_1172_ = l_Lean_MessageData_ofName(v_name_1135_);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__3, &l_Lean_Compiler_LCNF_nameToImpureType___closed__3_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__3);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v___x_1175_, v_a_1136_, v_a_1137_);
return v___x_1176_;
}
}
else
{
lean_dec(v_val_1155_);
lean_dec(v_name_1135_);
goto v___jp_1139_;
}
}
else
{
lean_dec(v___x_1154_);
lean_dec(v_name_1135_);
goto v___jp_1139_;
}
}
v___jp_1139_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_nameToImpureType___boxed(lean_object* v_name_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Compiler_LCNF_nameToImpureType(v_name_1177_, v_a_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0(lean_object* v_00_u03b1_1182_, lean_object* v_msg_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_msg_1183_, v___y_1184_, v___y_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___boxed(lean_object* v_00_u03b1_1188_, lean_object* v_msg_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0(v_00_u03b1_1188_, v_msg_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
return v_res_1193_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(lean_object* v_type_1195_){
_start:
{
switch(lean_obj_tag(v_type_1195_))
{
case 4:
{
lean_object* v_declName_1196_; 
v_declName_1196_ = lean_ctor_get(v_type_1195_, 0);
if (lean_obj_tag(v_declName_1196_) == 1)
{
lean_object* v_pre_1197_; 
v_pre_1197_ = lean_ctor_get(v_declName_1196_, 0);
if (lean_obj_tag(v_pre_1197_) == 0)
{
lean_object* v_str_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v_str_1198_ = lean_ctor_get(v_declName_1196_, 1);
v___x_1199_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___closed__0));
v___x_1200_ = lean_string_dec_eq(v_str_1198_, v___x_1199_);
return v___x_1200_;
}
else
{
uint8_t v___x_1201_; 
v___x_1201_ = 0;
return v___x_1201_;
}
}
else
{
uint8_t v___x_1202_; 
v___x_1202_ = 0;
return v___x_1202_;
}
}
case 7:
{
lean_object* v_body_1203_; 
v_body_1203_ = lean_ctor_get(v_type_1195_, 2);
v_type_1195_ = v_body_1203_;
goto _start;
}
default: 
{
uint8_t v___x_1205_; 
v___x_1205_ = 0;
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___boxed(lean_object* v_type_1206_){
_start:
{
uint8_t v_res_1207_; lean_object* v_r_1208_; 
v_res_1207_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(v_type_1206_);
lean_dec_ref(v_type_1206_);
v_r_1208_ = lean_box(v_res_1207_);
return v_r_1208_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(lean_object* v_msg_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___f_1213_; lean_object* v___x_747__overap_1214_; lean_object* v___x_1215_; 
v___f_1213_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0));
v___x_747__overap_1214_ = lean_panic_fn_borrowed(v___f_1213_, v_msg_1209_);
lean_inc(v___y_1211_);
lean_inc_ref(v___y_1210_);
v___x_1215_ = lean_apply_3(v___x_747__overap_1214_, v___y_1210_, v___y_1211_, lean_box(0));
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1___boxed(lean_object* v_msg_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(v_msg_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1220_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toImpureType___closed__1(void){
_start:
{
lean_object* v___x_1223_; lean_object* v_dummy_1224_; 
v___x_1223_ = lean_box(0);
v_dummy_1224_ = l_Lean_Expr_sort___override(v___x_1223_);
return v_dummy_1224_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toImpureType___closed__3(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1226_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__2));
v___x_1227_ = lean_unsigned_to_nat(41u);
v___x_1228_ = lean_unsigned_to_nat(139u);
v___x_1229_ = ((lean_object*)(l_Lean_Compiler_LCNF_toImpureType___closed__2));
v___x_1230_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__0));
v___x_1231_ = l_mkPanicMessageWithDecl(v___x_1230_, v___x_1229_, v___x_1228_, v___x_1227_, v___x_1226_);
return v___x_1231_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toImpureType___closed__4(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1232_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__2));
v___x_1233_ = lean_unsigned_to_nat(9u);
v___x_1234_ = lean_unsigned_to_nat(151u);
v___x_1235_ = ((lean_object*)(l_Lean_Compiler_LCNF_toImpureType___closed__2));
v___x_1236_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__0));
v___x_1237_ = l_mkPanicMessageWithDecl(v___x_1236_, v___x_1235_, v___x_1234_, v___x_1233_, v___x_1232_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpureType(lean_object* v_type_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
switch(lean_obj_tag(v_type_1238_))
{
case 4:
{
lean_object* v_declName_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_declName_1242_ = lean_ctor_get(v_type_1238_, 0);
lean_inc(v_declName_1242_);
lean_dec_ref_known(v_type_1238_, 2);
v___x_1243_ = ((lean_object*)(l_Lean_Compiler_LCNF_toImpureType___closed__0));
v___x_1244_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(v_declName_1242_, v___x_1243_, v_a_1239_, v_a_1240_);
return v___x_1244_;
}
case 5:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Expr_getAppFn(v_type_1238_);
if (lean_obj_tag(v___x_1245_) == 4)
{
lean_object* v_declName_1246_; lean_object* v_dummy_1247_; lean_object* v_nargs_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v_declName_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_declName_1246_);
lean_dec_ref_known(v___x_1245_, 2);
v_dummy_1247_ = lean_obj_once(&l_Lean_Compiler_LCNF_toImpureType___closed__1, &l_Lean_Compiler_LCNF_toImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_toImpureType___closed__1);
v_nargs_1248_ = l_Lean_Expr_getAppNumArgs(v_type_1238_);
lean_inc(v_nargs_1248_);
v___x_1249_ = lean_mk_array(v_nargs_1248_, v_dummy_1247_);
v___x_1250_ = lean_unsigned_to_nat(1u);
v___x_1251_ = lean_nat_sub(v_nargs_1248_, v___x_1250_);
lean_dec(v_nargs_1248_);
v___x_1252_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_type_1238_, v___x_1249_, v___x_1251_);
v___x_1253_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(v_declName_1246_, v___x_1252_, v_a_1239_, v_a_1240_);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec_ref(v___x_1245_);
lean_dec_ref_known(v_type_1238_, 2);
v___x_1254_ = lean_obj_once(&l_Lean_Compiler_LCNF_toImpureType___closed__3, &l_Lean_Compiler_LCNF_toImpureType___closed__3_once, _init_l_Lean_Compiler_LCNF_toImpureType___closed__3);
v___x_1255_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(v___x_1254_, v_a_1239_, v_a_1240_);
return v___x_1255_;
}
}
case 7:
{
lean_object* v_body_1256_; uint8_t v___x_1257_; 
v_body_1256_ = lean_ctor_get(v_type_1238_, 2);
lean_inc_ref(v_body_1256_);
lean_dec_ref_known(v_type_1238_, 3);
v___x_1257_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(v_body_1256_);
lean_dec_ref(v_body_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
else
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
}
case 10:
{
lean_object* v_expr_1262_; 
v_expr_1262_ = lean_ctor_get(v_type_1238_, 1);
lean_inc_ref(v_expr_1262_);
lean_dec_ref_known(v_type_1238_, 2);
v_type_1238_ = v_expr_1262_;
goto _start;
}
default: 
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec_ref(v_type_1238_);
v___x_1264_ = lean_obj_once(&l_Lean_Compiler_LCNF_toImpureType___closed__4, &l_Lean_Compiler_LCNF_toImpureType___closed__4_once, _init_l_Lean_Compiler_LCNF_toImpureType___closed__4);
v___x_1265_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(v___x_1264_, v_a_1239_, v_a_1240_);
return v___x_1265_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(lean_object* v_declName_1266_, lean_object* v_args_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = l_Lean_instInhabitedExpr;
lean_inc(v_declName_1266_);
v___x_1272_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_declName_1266_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
if (lean_obj_tag(v_a_1273_) == 1)
{
lean_object* v_val_1274_; lean_object* v_ctorName_1275_; lean_object* v_numParams_1276_; lean_object* v_fieldIdx_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_dec(v_declName_1266_);
v_val_1274_ = lean_ctor_get(v_a_1273_, 0);
lean_inc(v_val_1274_);
lean_dec_ref_known(v_a_1273_, 1);
v_ctorName_1275_ = lean_ctor_get(v_val_1274_, 0);
lean_inc(v_ctorName_1275_);
v_numParams_1276_ = lean_ctor_get(v_val_1274_, 1);
lean_inc(v_numParams_1276_);
v_fieldIdx_1277_ = lean_ctor_get(v_val_1274_, 2);
lean_inc(v_fieldIdx_1277_);
lean_dec(v_val_1274_);
v___x_1278_ = lean_box(0);
v___x_1279_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_ctorName_1275_, v___x_1278_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = l_Array_toSubarray___redArg(v_args_1267_, v___x_1281_, v_numParams_1276_);
v___x_1283_ = l_Subarray_copy___redArg(v___x_1282_);
v___x_1284_ = l_Lean_Compiler_LCNF_instantiateForall(v_a_1280_, v___x_1283_, v_a_1268_, v_a_1269_);
lean_dec_ref(v___x_1283_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = l_Lean_Compiler_LCNF_getParamTypes(v_a_1285_);
v___x_1287_ = lean_array_get(v___x_1271_, v___x_1286_, v_fieldIdx_1277_);
lean_dec(v_fieldIdx_1277_);
lean_dec_ref(v___x_1286_);
v___x_1288_ = l_Lean_Compiler_LCNF_toMonoType(v___x_1287_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1290_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v___x_1290_ = l_Lean_Compiler_LCNF_toImpureType(v_a_1289_, v_a_1268_, v_a_1269_);
return v___x_1290_;
}
else
{
return v___x_1288_;
}
}
else
{
lean_dec(v_fieldIdx_1277_);
return v___x_1284_;
}
}
else
{
lean_dec(v_fieldIdx_1277_);
lean_dec(v_numParams_1276_);
lean_dec_ref(v_args_1267_);
return v___x_1279_;
}
}
else
{
lean_object* v___x_1291_; 
lean_dec(v_a_1273_);
lean_dec_ref(v_args_1267_);
v___x_1291_ = l_Lean_Compiler_LCNF_nameToImpureType(v_declName_1266_, v_a_1268_, v_a_1269_);
return v___x_1291_;
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v_args_1267_);
lean_dec(v_declName_1266_);
v_a_1292_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1272_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1272_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp___boxed(lean_object* v_declName_1300_, lean_object* v_args_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(v_declName_1300_, v_args_1301_, v_a_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpureType___boxed(lean_object* v_type_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1306_, v_a_1307_, v_a_1308_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx___impl(lean_object* v_x_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_obj_tag_nat(v_x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx___impl___boxed(lean_object* v_x_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx___impl(v_x_1313_);
lean_dec(v_x_1313_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(lean_object* v_t_1315_, lean_object* v_k_1316_){
_start:
{
switch(lean_obj_tag(v_t_1315_))
{
case 1:
{
lean_object* v_i_1317_; lean_object* v_type_1318_; lean_object* v___x_1319_; 
v_i_1317_ = lean_ctor_get(v_t_1315_, 0);
lean_inc(v_i_1317_);
v_type_1318_ = lean_ctor_get(v_t_1315_, 1);
lean_inc_ref(v_type_1318_);
lean_dec_ref_known(v_t_1315_, 2);
v___x_1319_ = lean_apply_2(v_k_1316_, v_i_1317_, v_type_1318_);
return v___x_1319_;
}
case 2:
{
lean_object* v_i_1320_; lean_object* v___x_1321_; 
v_i_1320_ = lean_ctor_get(v_t_1315_, 0);
lean_inc(v_i_1320_);
lean_dec_ref_known(v_t_1315_, 1);
v___x_1321_ = lean_apply_1(v_k_1316_, v_i_1320_);
return v___x_1321_;
}
case 3:
{
lean_object* v_sz_1322_; lean_object* v_offset_1323_; lean_object* v_type_1324_; lean_object* v___x_1325_; 
v_sz_1322_ = lean_ctor_get(v_t_1315_, 0);
lean_inc(v_sz_1322_);
v_offset_1323_ = lean_ctor_get(v_t_1315_, 1);
lean_inc(v_offset_1323_);
v_type_1324_ = lean_ctor_get(v_t_1315_, 2);
lean_inc_ref(v_type_1324_);
lean_dec_ref_known(v_t_1315_, 3);
v___x_1325_ = lean_apply_3(v_k_1316_, v_sz_1322_, v_offset_1323_, v_type_1324_);
return v___x_1325_;
}
case 5:
{
lean_object* v_depth_1326_; lean_object* v_i_1327_; lean_object* v_type_1328_; lean_object* v___x_1329_; 
v_depth_1326_ = lean_ctor_get(v_t_1315_, 0);
lean_inc(v_depth_1326_);
v_i_1327_ = lean_ctor_get(v_t_1315_, 1);
lean_inc(v_i_1327_);
v_type_1328_ = lean_ctor_get(v_t_1315_, 2);
lean_inc_ref(v_type_1328_);
lean_dec_ref_known(v_t_1315_, 3);
v___x_1329_ = lean_apply_3(v_k_1316_, v_depth_1326_, v_i_1327_, v_type_1328_);
return v___x_1329_;
}
default: 
{
lean_dec(v_t_1315_);
return v_k_1316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim(lean_object* v_motive_1330_, lean_object* v_ctorIdx_1331_, lean_object* v_t_1332_, lean_object* v_h_1333_, lean_object* v_k_1334_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1332_, v_k_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___boxed(lean_object* v_motive_1336_, lean_object* v_ctorIdx_1337_, lean_object* v_t_1338_, lean_object* v_h_1339_, lean_object* v_k_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim(v_motive_1336_, v_ctorIdx_1337_, v_t_1338_, v_h_1339_, v_k_1340_);
lean_dec(v_ctorIdx_1337_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_erased_elim___redArg(lean_object* v_t_1342_, lean_object* v_erased_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1342_, v_erased_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_erased_elim(lean_object* v_motive_1345_, lean_object* v_t_1346_, lean_object* v_h_1347_, lean_object* v_erased_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1346_, v_erased_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_object_elim___redArg(lean_object* v_t_1350_, lean_object* v_object_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1350_, v_object_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_object_elim(lean_object* v_motive_1353_, lean_object* v_t_1354_, lean_object* v_h_1355_, lean_object* v_object_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1354_, v_object_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_usize_elim___redArg(lean_object* v_t_1358_, lean_object* v_usize_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1358_, v_usize_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_usize_elim(lean_object* v_motive_1361_, lean_object* v_t_1362_, lean_object* v_h_1363_, lean_object* v_usize_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1362_, v_usize_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_scalar_elim___redArg(lean_object* v_t_1366_, lean_object* v_scalar_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1366_, v_scalar_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_scalar_elim(lean_object* v_motive_1369_, lean_object* v_t_1370_, lean_object* v_h_1371_, lean_object* v_scalar_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1370_, v_scalar_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_void_elim___redArg(lean_object* v_t_1374_, lean_object* v_void_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1374_, v_void_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_void_elim(lean_object* v_motive_1377_, lean_object* v_t_1378_, lean_object* v_h_1379_, lean_object* v_void_1380_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1378_, v_void_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_spilled_elim___redArg(lean_object* v_t_1382_, lean_object* v_spilled_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1382_, v_spilled_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_spilled_elim(lean_object* v_motive_1385_, lean_object* v_t_1386_, lean_object* v_h_1387_, lean_object* v_spilled_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1386_, v_spilled_1388_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo_default(void){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_box(0);
return v___x_1390_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo(void){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_box(0);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format(lean_object* v_x_1416_){
_start:
{
switch(lean_obj_tag(v_x_1416_))
{
case 0:
{
lean_object* v___x_1417_; 
v___x_1417_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__1));
return v___x_1417_;
}
case 1:
{
lean_object* v_i_1418_; lean_object* v_type_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1434_; 
v_i_1418_ = lean_ctor_get(v_x_1416_, 0);
v_type_1419_ = lean_ctor_get(v_x_1416_, 1);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_x_1416_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1421_ = v_x_1416_;
v_isShared_1422_ = v_isSharedCheck_1434_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_type_1419_);
lean_inc(v_i_1418_);
lean_dec(v_x_1416_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1434_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1423_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__3));
v___x_1424_ = l_Nat_reprFast(v_i_1418_);
v___x_1425_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set_tag(v___x_1421_, 5);
lean_ctor_set(v___x_1421_, 1, v___x_1425_);
lean_ctor_set(v___x_1421_, 0, v___x_1423_);
v___x_1427_ = v___x_1421_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1428_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5));
v___x_1429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = lean_expr_dbg_to_string(v_type_1419_);
lean_dec_ref(v_type_1419_);
v___x_1431_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
v___x_1432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1429_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
return v___x_1432_;
}
}
}
case 2:
{
lean_object* v_i_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1445_; 
v_i_1435_ = lean_ctor_get(v_x_1416_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_x_1416_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1437_ = v_x_1416_;
v_isShared_1438_ = v_isSharedCheck_1445_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_i_1435_);
lean_dec(v_x_1416_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1445_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1439_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__7));
v___x_1440_ = l_Nat_reprFast(v_i_1435_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set_tag(v___x_1437_, 3);
lean_ctor_set(v___x_1437_, 0, v___x_1440_);
v___x_1442_ = v___x_1437_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1439_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
return v___x_1443_;
}
}
}
case 3:
{
lean_object* v_sz_1446_; lean_object* v_offset_1447_; lean_object* v_type_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_sz_1446_ = lean_ctor_get(v_x_1416_, 0);
lean_inc(v_sz_1446_);
v_offset_1447_ = lean_ctor_get(v_x_1416_, 1);
lean_inc(v_offset_1447_);
v_type_1448_ = lean_ctor_get(v_x_1416_, 2);
lean_inc_ref(v_type_1448_);
lean_dec_ref_known(v_x_1416_, 3);
v___x_1449_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__9));
v___x_1450_ = l_Nat_reprFast(v_sz_1446_);
v___x_1451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
v___x_1452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1449_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__11));
v___x_1454_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1452_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
v___x_1455_ = l_Nat_reprFast(v_offset_1447_);
v___x_1456_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
v___x_1457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1454_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5));
v___x_1459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1457_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
v___x_1460_ = lean_expr_dbg_to_string(v_type_1448_);
lean_dec_ref(v_type_1448_);
v___x_1461_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
v___x_1462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1459_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
return v___x_1462_;
}
case 4:
{
lean_object* v___x_1463_; 
v___x_1463_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__13));
return v___x_1463_;
}
default: 
{
lean_object* v_depth_1464_; lean_object* v_i_1465_; lean_object* v_type_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_depth_1464_ = lean_ctor_get(v_x_1416_, 0);
lean_inc(v_depth_1464_);
v_i_1465_ = lean_ctor_get(v_x_1416_, 1);
lean_inc(v_i_1465_);
v_type_1466_ = lean_ctor_get(v_x_1416_, 2);
lean_inc_ref(v_type_1466_);
lean_dec_ref_known(v_x_1416_, 3);
v___x_1467_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__3));
v___x_1468_ = l_Nat_reprFast(v_depth_1464_);
v___x_1469_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
v___x_1470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1467_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__15));
v___x_1472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1470_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = l_Nat_reprFast(v_i_1465_);
v___x_1474_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
v___x_1475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1472_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5));
v___x_1477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = lean_expr_dbg_to_string(v_type_1466_);
lean_dec_ref(v_type_1466_);
v___x_1479_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
v___x_1480_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1477_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
return v___x_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_spillDepth(lean_object* v_x_1481_){
_start:
{
if (lean_obj_tag(v_x_1481_) == 5)
{
lean_object* v_depth_1482_; 
v_depth_1482_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_depth_1482_);
return v_depth_1482_;
}
else
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_unsigned_to_nat(0u);
return v___x_1483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_spillDepth___boxed(lean_object* v_x_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_Compiler_LCNF_CtorFieldInfo_spillDepth(v_x_1484_);
lean_dec(v_x_1484_);
return v_res_1485_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_spillLinkIdx___closed__0(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1488_ = lean_unsigned_to_nat(1u);
v___x_1489_ = l_Lean_maxCtorNumObjs;
v___x_1490_ = lean_nat_sub(v___x_1489_, v___x_1488_);
return v___x_1490_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_spillLinkIdx(void){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_obj_once(&l_Lean_Compiler_LCNF_spillLinkIdx___closed__0, &l_Lean_Compiler_LCNF_spillLinkIdx___closed__0_once, _init_l_Lean_Compiler_LCNF_spillLinkIdx___closed__0);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_numSpillObjs(lean_object* v_numObjs_1492_){
_start:
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = l_Lean_maxCtorNumObjs;
v___x_1494_ = lean_nat_dec_le(v_numObjs_1492_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1495_ = lean_unsigned_to_nat(1u);
v___x_1496_ = lean_nat_sub(v_numObjs_1492_, v___x_1495_);
v___x_1497_ = l_Lean_Compiler_LCNF_spillLinkIdx;
v___x_1498_ = lean_nat_div(v___x_1496_, v___x_1497_);
lean_dec(v___x_1496_);
return v___x_1498_;
}
else
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_unsigned_to_nat(0u);
return v___x_1499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_numSpillObjs___boxed(lean_object* v_numObjs_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Compiler_LCNF_numSpillObjs(v_numObjs_1500_);
lean_dec(v_numObjs_1500_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_spillCtorInfo(lean_object* v_ctorName_1505_, lean_object* v_size_1506_){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1507_ = ((lean_object*)(l_Lean_Compiler_LCNF_spillCtorInfo___closed__1));
v___x_1508_ = l_Lean_Name_append(v_ctorName_1505_, v___x_1507_);
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1508_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
lean_ctor_set(v___x_1510_, 2, v_size_1506_);
lean_ctor_set(v___x_1510_, 3, v___x_1509_);
lean_ctor_set(v___x_1510_, 4, v___x_1509_);
return v___x_1510_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0));
v___x_1514_ = l_Lean_Compiler_LCNF_instInhabitedCtorInfo_default;
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
lean_ctor_set(v___x_1515_, 1, v___x_1513_);
return v___x_1515_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default(void){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout(void){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_init_1518_, lean_object* v_x_1519_){
_start:
{
if (lean_obj_tag(v_x_1519_) == 0)
{
lean_object* v_k_1520_; lean_object* v_v_1521_; lean_object* v_l_1522_; lean_object* v_r_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_k_1520_ = lean_ctor_get(v_x_1519_, 1);
v_v_1521_ = lean_ctor_get(v_x_1519_, 2);
v_l_1522_ = lean_ctor_get(v_x_1519_, 3);
v_r_1523_ = lean_ctor_get(v_x_1519_, 4);
v___x_1524_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(v_init_1518_, v_l_1522_);
lean_inc(v_v_1521_);
lean_inc(v_k_1520_);
v___x_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1525_, 0, v_k_1520_);
lean_ctor_set(v___x_1525_, 1, v_v_1521_);
v___x_1526_ = lean_array_push(v___x_1524_, v___x_1525_);
v_init_1518_ = v___x_1526_;
v_x_1519_ = v_r_1523_;
goto _start;
}
else
{
return v_init_1518_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_init_1528_, lean_object* v_x_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(v_init_1528_, v_x_1529_);
lean_dec(v_x_1529_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2(lean_object* v_env_1531_, lean_object* v_as_1532_, size_t v_i_1533_, size_t v_stop_1534_, lean_object* v_b_1535_){
_start:
{
lean_object* v___y_1537_; uint8_t v___x_1541_; 
v___x_1541_ = lean_usize_dec_eq(v_i_1533_, v_stop_1534_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v_fst_1543_; uint8_t v___x_1544_; 
v___x_1542_ = lean_array_uget_borrowed(v_as_1532_, v_i_1533_);
v_fst_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_fst_1543_);
lean_inc_ref(v_env_1531_);
v___x_1544_ = l_Lean_Environment_contains(v_env_1531_, v_fst_1543_, v___x_1541_);
if (v___x_1544_ == 0)
{
v___y_1537_ = v_b_1535_;
goto v___jp_1536_;
}
else
{
lean_object* v___x_1545_; 
lean_inc(v___x_1542_);
v___x_1545_ = lean_array_push(v_b_1535_, v___x_1542_);
v___y_1537_ = v___x_1545_;
goto v___jp_1536_;
}
}
else
{
lean_dec_ref(v_env_1531_);
return v_b_1535_;
}
v___jp_1536_:
{
size_t v___x_1538_; size_t v___x_1539_; 
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_add(v_i_1533_, v___x_1538_);
v_i_1533_ = v___x_1539_;
v_b_1535_ = v___y_1537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_1546_, lean_object* v_as_1547_, lean_object* v_i_1548_, lean_object* v_stop_1549_, lean_object* v_b_1550_){
_start:
{
size_t v_i_boxed_1551_; size_t v_stop_boxed_1552_; lean_object* v_res_1553_; 
v_i_boxed_1551_ = lean_unbox_usize(v_i_1548_);
lean_dec(v_i_1548_);
v_stop_boxed_1552_ = lean_unbox_usize(v_stop_1549_);
lean_dec(v_stop_1549_);
v_res_1553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2(v_env_1546_, v_as_1547_, v_i_boxed_1551_, v_stop_boxed_1552_, v_b_1550_);
lean_dec_ref(v_as_1547_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(lean_object* v_env_1554_, lean_object* v_as_1555_, size_t v_i_1556_, size_t v_stop_1557_, lean_object* v_b_1558_){
_start:
{
lean_object* v___y_1560_; uint8_t v___x_1564_; 
v___x_1564_ = lean_usize_dec_eq(v_i_1556_, v_stop_1557_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v_fst_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1565_ = lean_array_uget_borrowed(v_as_1555_, v_i_1556_);
v_fst_1566_ = lean_ctor_get(v___x_1565_, 0);
v___x_1567_ = 1;
lean_inc_ref(v_env_1554_);
v___x_1568_ = l_Lean_Environment_setExporting(v_env_1554_, v___x_1567_);
lean_inc(v_fst_1566_);
v___x_1569_ = l_Lean_Environment_contains(v___x_1568_, v_fst_1566_, v___x_1564_);
if (v___x_1569_ == 0)
{
v___y_1560_ = v_b_1558_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1570_; 
lean_inc(v___x_1565_);
v___x_1570_ = lean_array_push(v_b_1558_, v___x_1565_);
v___y_1560_ = v___x_1570_;
goto v___jp_1559_;
}
}
else
{
lean_dec_ref(v_env_1554_);
return v_b_1558_;
}
v___jp_1559_:
{
size_t v___x_1561_; size_t v___x_1562_; 
v___x_1561_ = ((size_t)1ULL);
v___x_1562_ = lean_usize_add(v_i_1556_, v___x_1561_);
v_i_1556_ = v___x_1562_;
v_b_1558_ = v___y_1560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_1571_, lean_object* v_as_1572_, lean_object* v_i_1573_, lean_object* v_stop_1574_, lean_object* v_b_1575_){
_start:
{
size_t v_i_boxed_1576_; size_t v_stop_boxed_1577_; lean_object* v_res_1578_; 
v_i_boxed_1576_ = lean_unbox_usize(v_i_1573_);
lean_dec(v_i_1573_);
v_stop_boxed_1577_ = lean_unbox_usize(v_stop_1574_);
lean_dec(v_stop_1574_);
v_res_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(v_env_1571_, v_as_1572_, v_i_boxed_1576_, v_stop_boxed_1577_, v_b_1575_);
lean_dec_ref(v_as_1572_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(lean_object* v___x_1579_, lean_object* v_env_1580_, lean_object* v_s_1581_){
_start:
{
lean_object* v___y_1583_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1592_ = lean_mk_empty_array_with_capacity(v___x_1579_);
v___x_1593_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(v___x_1592_, v_s_1581_);
v___x_1594_ = lean_array_get_size(v___x_1593_);
v___x_1595_ = lean_mk_empty_array_with_capacity(v___x_1579_);
v___x_1596_ = lean_nat_dec_lt(v___x_1579_, v___x_1594_);
if (v___x_1596_ == 0)
{
lean_dec_ref(v___x_1593_);
v___y_1583_ = v___x_1595_;
goto v___jp_1582_;
}
else
{
size_t v___x_1597_; size_t v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = ((size_t)0ULL);
v___x_1598_ = lean_usize_of_nat(v___x_1594_);
lean_inc_ref(v_env_1580_);
v___x_1599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2(v_env_1580_, v___x_1593_, v___x_1597_, v___x_1598_, v___x_1595_);
lean_dec_ref(v___x_1593_);
v___y_1583_ = v___x_1599_;
goto v___jp_1582_;
}
v___jp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1584_ = lean_array_get_size(v___y_1583_);
v___x_1585_ = lean_mk_empty_array_with_capacity(v___x_1579_);
v___x_1586_ = lean_nat_dec_lt(v___x_1579_, v___x_1584_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; 
lean_dec_ref(v_env_1580_);
lean_inc_ref(v___x_1585_);
v___x_1587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1585_);
lean_ctor_set(v___x_1587_, 2, v___y_1583_);
return v___x_1587_;
}
else
{
size_t v___x_1588_; size_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1588_ = ((size_t)0ULL);
v___x_1589_ = lean_usize_of_nat(v___x_1584_);
v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(v_env_1580_, v___y_1583_, v___x_1588_, v___x_1589_, v___x_1585_);
lean_inc_ref(v___x_1590_);
v___x_1591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
lean_ctor_set(v___x_1591_, 2, v___y_1583_);
return v___x_1591_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2____boxed(lean_object* v___x_1600_, lean_object* v_env_1601_, lean_object* v_s_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(v___x_1600_, v_env_1601_, v_s_1602_);
lean_dec(v_s_1602_);
lean_dec(v___x_1600_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; lean_object* v___x_1615_; 
v___f_1611_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_));
v___x_1612_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_));
v___x_1613_ = lean_box(0);
v___x_1614_ = 0;
v___x_1615_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_1612_, v___x_1613_, v___x_1614_, v___f_1611_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2____boxed(lean_object* v_a_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_();
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(lean_object* v_init_1618_, lean_object* v_t_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(v_init_1618_, v_t_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1___boxed(lean_object* v_init_1621_, lean_object* v_t_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(v_init_1621_, v_t_1622_);
lean_dec(v_t_1622_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout(lean_object* v_layout_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_ctorInfo_1628_; lean_object* v___x_1629_; 
v_ctorInfo_1628_ = lean_ctor_get(v_layout_1624_, 0);
lean_inc_ref(v_ctorInfo_1628_);
lean_dec_ref(v_layout_1624_);
v___x_1629_ = l_Lean_Compiler_LCNF_CtorInfo_checkValid(v_ctorInfo_1628_, v_a_1625_, v_a_1626_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout___boxed(lean_object* v_layout_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout(v_layout_1630_, v_a_1631_, v_a_1632_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(lean_object* v_msg_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___f_1639_; lean_object* v___x_12016__overap_1640_; lean_object* v___x_1641_; 
v___f_1639_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0));
v___x_12016__overap_1640_ = lean_panic_fn_borrowed(v___f_1639_, v_msg_1635_);
lean_inc(v___y_1637_);
lean_inc_ref(v___y_1636_);
v___x_1641_ = lean_apply_3(v___x_12016__overap_1640_, v___y_1636_, v___y_1637_, lean_box(0));
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1___boxed(lean_object* v_msg_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(v_msg_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(lean_object* v_msg_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___f_1654_; lean_object* v___x_12026__overap_1655_; lean_object* v___x_1656_; 
v___f_1654_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___closed__0));
v___x_12026__overap_1655_ = lean_panic_fn_borrowed(v___f_1654_, v_msg_1648_);
lean_inc(v___y_1652_);
lean_inc_ref(v___y_1651_);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1649_);
v___x_1656_ = lean_apply_5(v___x_12026__overap_1655_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, lean_box(0));
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___boxed(lean_object* v_msg_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(v_msg_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___redArg(lean_object* v_type_1664_, lean_object* v_k_1665_, uint8_t v_cleanupAnnotations_1666_, uint8_t v_whnfType_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___f_1673_; lean_object* v___x_1674_; 
v___f_1673_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1673_, 0, v_k_1665_);
v___x_1674_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1664_, v___f_1673_, v_cleanupAnnotations_1666_, v_whnfType_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_a_1683_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1674_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1674_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___redArg___boxed(lean_object* v_type_1691_, lean_object* v_k_1692_, lean_object* v_cleanupAnnotations_1693_, lean_object* v_whnfType_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1700_; uint8_t v_whnfType_boxed_1701_; lean_object* v_res_1702_; 
v_cleanupAnnotations_boxed_1700_ = lean_unbox(v_cleanupAnnotations_1693_);
v_whnfType_boxed_1701_ = lean_unbox(v_whnfType_1694_);
v_res_1702_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___redArg(v_type_1691_, v_k_1692_, v_cleanupAnnotations_boxed_1700_, v_whnfType_boxed_1701_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6(lean_object* v_00_u03b1_1703_, lean_object* v_type_1704_, lean_object* v_k_1705_, uint8_t v_cleanupAnnotations_1706_, uint8_t v_whnfType_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___redArg(v_type_1704_, v_k_1705_, v_cleanupAnnotations_1706_, v_whnfType_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___boxed(lean_object* v_00_u03b1_1714_, lean_object* v_type_1715_, lean_object* v_k_1716_, lean_object* v_cleanupAnnotations_1717_, lean_object* v_whnfType_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1724_; uint8_t v_whnfType_boxed_1725_; lean_object* v_res_1726_; 
v_cleanupAnnotations_boxed_1724_ = lean_unbox(v_cleanupAnnotations_1717_);
v_whnfType_boxed_1725_ = lean_unbox(v_whnfType_1718_);
v_res_1726_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6(v_00_u03b1_1714_, v_type_1715_, v_k_1716_, v_cleanupAnnotations_boxed_1724_, v_whnfType_boxed_1725_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(lean_object* v_size_1727_, size_t v_sz_1728_, size_t v_i_1729_, lean_object* v_bs_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v___x_1732_; 
v___x_1732_ = lean_usize_dec_lt(v_i_1729_, v_sz_1728_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_bs_1730_);
lean_ctor_set(v___x_1733_, 1, v___y_1731_);
return v___x_1733_;
}
else
{
lean_object* v_v_1734_; lean_object* v___x_1735_; lean_object* v_bs_x27_1736_; lean_object* v_fst_1738_; lean_object* v_snd_1739_; 
v_v_1734_ = lean_array_uget(v_bs_1730_, v_i_1729_);
v___x_1735_ = lean_unsigned_to_nat(0u);
v_bs_x27_1736_ = lean_array_uset(v_bs_1730_, v_i_1729_, v___x_1735_);
if (lean_obj_tag(v_v_1734_) == 3)
{
lean_object* v_sz_1744_; lean_object* v_type_1745_; uint8_t v___x_1746_; 
v_sz_1744_ = lean_ctor_get(v_v_1734_, 0);
v_type_1745_ = lean_ctor_get(v_v_1734_, 2);
v___x_1746_ = lean_nat_dec_eq(v_sz_1744_, v_size_1727_);
if (v___x_1746_ == 0)
{
v_fst_1738_ = v_v_1734_;
v_snd_1739_ = v___y_1731_;
goto v___jp_1737_;
}
else
{
lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1754_; 
lean_inc_ref(v_type_1745_);
lean_inc(v_sz_1744_);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_v_1734_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; lean_object* v_unused_1756_; lean_object* v_unused_1757_; 
v_unused_1755_ = lean_ctor_get(v_v_1734_, 2);
lean_dec(v_unused_1755_);
v_unused_1756_ = lean_ctor_get(v_v_1734_, 1);
lean_dec(v_unused_1756_);
v_unused_1757_ = lean_ctor_get(v_v_1734_, 0);
lean_dec(v_unused_1757_);
v___x_1748_ = v_v_1734_;
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
else
{
lean_dec(v_v_1734_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1750_ = lean_nat_add(v___y_1731_, v_sz_1744_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v___y_1731_);
v___x_1752_ = v___x_1748_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_sz_1744_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v___y_1731_);
lean_ctor_set(v_reuseFailAlloc_1753_, 2, v_type_1745_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
v_fst_1738_ = v___x_1752_;
v_snd_1739_ = v___x_1750_;
goto v___jp_1737_;
}
}
}
}
else
{
v_fst_1738_ = v_v_1734_;
v_snd_1739_ = v___y_1731_;
goto v___jp_1737_;
}
v___jp_1737_:
{
size_t v___x_1740_; size_t v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = ((size_t)1ULL);
v___x_1741_ = lean_usize_add(v_i_1729_, v___x_1740_);
v___x_1742_ = lean_array_uset(v_bs_x27_1736_, v_i_1729_, v_fst_1738_);
v_i_1729_ = v___x_1741_;
v_bs_1730_ = v___x_1742_;
v___y_1731_ = v_snd_1739_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0___boxed(lean_object* v_size_1758_, lean_object* v_sz_1759_, lean_object* v_i_1760_, lean_object* v_bs_1761_, lean_object* v___y_1762_){
_start:
{
size_t v_sz_boxed_1763_; size_t v_i_boxed_1764_; lean_object* v_res_1765_; 
v_sz_boxed_1763_ = lean_unbox_usize(v_sz_1759_);
lean_dec(v_sz_1759_);
v_i_boxed_1764_ = lean_unbox_usize(v_i_1760_);
lean_dec(v_i_1760_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(v_size_1758_, v_sz_boxed_1763_, v_i_boxed_1764_, v_bs_1761_, v___y_1762_);
lean_dec(v_size_1758_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0(lean_object* v_fields_1766_, lean_object* v_size_1767_, lean_object* v_nextOffset_1768_){
_start:
{
size_t v_sz_1769_; size_t v___x_1770_; lean_object* v___x_1771_; 
v_sz_1769_ = lean_array_size(v_fields_1766_);
v___x_1770_ = ((size_t)0ULL);
v___x_1771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(v_size_1767_, v_sz_1769_, v___x_1770_, v_fields_1766_, v_nextOffset_1768_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0___boxed(lean_object* v_fields_1772_, lean_object* v_size_1773_, lean_object* v_nextOffset_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0(v_fields_1772_, v_size_1773_, v_nextOffset_1774_);
lean_dec(v_size_1773_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5(size_t v_sz_1776_, size_t v_i_1777_, lean_object* v_bs_1778_){
_start:
{
uint8_t v___x_1779_; 
v___x_1779_ = lean_usize_dec_lt(v_i_1777_, v_sz_1776_);
if (v___x_1779_ == 0)
{
return v_bs_1778_;
}
else
{
lean_object* v_v_1780_; lean_object* v___x_1781_; lean_object* v_bs_x27_1782_; lean_object* v___y_1784_; 
v_v_1780_ = lean_array_uget(v_bs_1778_, v_i_1777_);
v___x_1781_ = lean_unsigned_to_nat(0u);
v_bs_x27_1782_ = lean_array_uset(v_bs_1778_, v_i_1777_, v___x_1781_);
if (lean_obj_tag(v_v_1780_) == 1)
{
lean_object* v_i_1789_; lean_object* v_type_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v_i_1789_ = lean_ctor_get(v_v_1780_, 0);
v_type_1790_ = lean_ctor_get(v_v_1780_, 1);
v___x_1791_ = l_Lean_Compiler_LCNF_spillLinkIdx;
v___x_1792_ = lean_nat_div(v_i_1789_, v___x_1791_);
v___x_1793_ = lean_nat_dec_eq(v___x_1792_, v___x_1781_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_inc_ref(v_type_1790_);
lean_inc(v_i_1789_);
lean_dec_ref_known(v_v_1780_, 2);
v___x_1794_ = lean_nat_mod(v_i_1789_, v___x_1791_);
lean_dec(v_i_1789_);
v___x_1795_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1792_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
lean_ctor_set(v___x_1795_, 2, v_type_1790_);
v___y_1784_ = v___x_1795_;
goto v___jp_1783_;
}
else
{
lean_dec(v___x_1792_);
v___y_1784_ = v_v_1780_;
goto v___jp_1783_;
}
}
else
{
v___y_1784_ = v_v_1780_;
goto v___jp_1783_;
}
v___jp_1783_:
{
size_t v___x_1785_; size_t v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = ((size_t)1ULL);
v___x_1786_ = lean_usize_add(v_i_1777_, v___x_1785_);
v___x_1787_ = lean_array_uset(v_bs_x27_1782_, v_i_1777_, v___y_1784_);
v_i_1777_ = v___x_1786_;
v_bs_1778_ = v___x_1787_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___boxed(lean_object* v_sz_1796_, lean_object* v_i_1797_, lean_object* v_bs_1798_){
_start:
{
size_t v_sz_boxed_1799_; size_t v_i_boxed_1800_; lean_object* v_res_1801_; 
v_sz_boxed_1799_ = lean_unbox_usize(v_sz_1796_);
lean_dec(v_sz_1796_);
v_i_boxed_1800_ = lean_unbox_usize(v_i_1797_);
lean_dec(v_i_1797_);
v_res_1801_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5(v_sz_boxed_1799_, v_i_boxed_1800_, v_bs_1798_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(size_t v_sz_1802_, size_t v_i_1803_, lean_object* v_bs_1804_, lean_object* v___y_1805_){
_start:
{
uint8_t v___x_1806_; 
v___x_1806_ = lean_usize_dec_lt(v_i_1803_, v_sz_1802_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v_bs_1804_);
lean_ctor_set(v___x_1807_, 1, v___y_1805_);
return v___x_1807_;
}
else
{
lean_object* v_v_1808_; lean_object* v___x_1809_; lean_object* v_bs_x27_1810_; lean_object* v_fst_1812_; lean_object* v_snd_1813_; 
v_v_1808_ = lean_array_uget(v_bs_1804_, v_i_1803_);
v___x_1809_ = lean_unsigned_to_nat(0u);
v_bs_x27_1810_ = lean_array_uset(v_bs_1804_, v_i_1803_, v___x_1809_);
if (lean_obj_tag(v_v_1808_) == 2)
{
lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1826_; 
v_isSharedCheck_1826_ = !lean_is_exclusive(v_v_1808_);
if (v_isSharedCheck_1826_ == 0)
{
lean_object* v_unused_1827_; 
v_unused_1827_ = lean_ctor_get(v_v_1808_, 0);
lean_dec(v_unused_1827_);
v___x_1819_ = v_v_1808_;
v_isShared_1820_ = v_isSharedCheck_1826_;
goto v_resetjp_1818_;
}
else
{
lean_dec(v_v_1808_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1826_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1821_ = lean_unsigned_to_nat(1u);
v___x_1822_ = lean_nat_add(v___y_1805_, v___x_1821_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___y_1805_);
v___x_1824_ = v___x_1819_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___y_1805_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
v_fst_1812_ = v___x_1824_;
v_snd_1813_ = v___x_1822_;
goto v___jp_1811_;
}
}
}
else
{
v_fst_1812_ = v_v_1808_;
v_snd_1813_ = v___y_1805_;
goto v___jp_1811_;
}
v___jp_1811_:
{
size_t v___x_1814_; size_t v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = ((size_t)1ULL);
v___x_1815_ = lean_usize_add(v_i_1803_, v___x_1814_);
v___x_1816_ = lean_array_uset(v_bs_x27_1810_, v_i_1803_, v_fst_1812_);
v_i_1803_ = v___x_1815_;
v_bs_1804_ = v___x_1816_;
v___y_1805_ = v_snd_1813_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4___boxed(lean_object* v_sz_1828_, lean_object* v_i_1829_, lean_object* v_bs_1830_, lean_object* v___y_1831_){
_start:
{
size_t v_sz_boxed_1832_; size_t v_i_boxed_1833_; lean_object* v_res_1834_; 
v_sz_boxed_1832_ = lean_unbox_usize(v_sz_1828_);
lean_dec(v_sz_1828_);
v_i_boxed_1833_ = lean_unbox_usize(v_i_1829_);
lean_dec(v_i_1829_);
v_res_1834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(v_sz_boxed_1832_, v_i_boxed_1833_, v_bs_1830_, v___y_1831_);
return v_res_1834_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1836_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__2));
v___x_1837_ = lean_unsigned_to_nat(15u);
v___x_1838_ = lean_unsigned_to_nat(266u);
v___x_1839_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0));
v___x_1840_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__0));
v___x_1841_ = l_mkPanicMessageWithDecl(v___x_1840_, v___x_1839_, v___x_1838_, v___x_1837_, v___x_1836_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(lean_object* v___f_1842_, lean_object* v_fst_1843_, lean_object* v_fst_1844_, lean_object* v_fst_1845_, lean_object* v_fst_1846_, lean_object* v_snd_1847_, lean_object* v_x_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1);
v___x_1855_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(v___x_1854_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1857_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1855_, 1);
lean_inc(v___y_1852_);
lean_inc_ref(v___y_1851_);
lean_inc(v___y_1850_);
lean_inc_ref(v___y_1849_);
v___x_1857_ = lean_apply_11(v___f_1842_, v_a_1856_, v_fst_1843_, v_fst_1844_, v_fst_1845_, v_fst_1846_, v_snd_1847_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, lean_box(0));
return v___x_1857_;
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v_snd_1847_);
lean_dec(v_fst_1846_);
lean_dec(v_fst_1845_);
lean_dec(v_fst_1844_);
lean_dec(v_fst_1843_);
lean_dec_ref(v___f_1842_);
v_a_1858_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1855_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1855_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___boxed(lean_object* v___f_1866_, lean_object* v_fst_1867_, lean_object* v_fst_1868_, lean_object* v_fst_1869_, lean_object* v_fst_1870_, lean_object* v_snd_1871_, lean_object* v_x_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1866_, v_fst_1867_, v_fst_1868_, v_fst_1869_, v_fst_1870_, v_snd_1871_, v_x_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec_ref(v_x_1872_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(lean_object* v_fst_1879_, lean_object* v_ctorField_1880_, lean_object* v_nextIdx_1881_, uint8_t v_has1BScalar_1882_, uint8_t v_has2BScalar_1883_, uint8_t v_has4BScalar_1884_, uint8_t v_has8BScalar_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1891_ = lean_array_push(v_fst_1879_, v_ctorField_1880_);
v___x_1892_ = lean_box(v_has4BScalar_1884_);
v___x_1893_ = lean_box(v_has8BScalar_1885_);
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = lean_box(v_has2BScalar_1883_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v___x_1894_);
v___x_1897_ = lean_box(v_has1BScalar_1882_);
v___x_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
lean_ctor_set(v___x_1898_, 1, v___x_1896_);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v_nextIdx_1881_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1891_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0___boxed(lean_object* v_fst_1903_, lean_object* v_ctorField_1904_, lean_object* v_nextIdx_1905_, lean_object* v_has1BScalar_1906_, lean_object* v_has2BScalar_1907_, lean_object* v_has4BScalar_1908_, lean_object* v_has8BScalar_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
uint8_t v_has1BScalar_boxed_1915_; uint8_t v_has2BScalar_boxed_1916_; uint8_t v_has4BScalar_boxed_1917_; uint8_t v_has8BScalar_boxed_1918_; lean_object* v_res_1919_; 
v_has1BScalar_boxed_1915_ = lean_unbox(v_has1BScalar_1906_);
v_has2BScalar_boxed_1916_ = lean_unbox(v_has2BScalar_1907_);
v_has4BScalar_boxed_1917_ = lean_unbox(v_has4BScalar_1908_);
v_has8BScalar_boxed_1918_ = lean_unbox(v_has8BScalar_1909_);
v_res_1919_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1903_, v_ctorField_1904_, v_nextIdx_1905_, v_has1BScalar_boxed_1915_, v_has2BScalar_boxed_1916_, v_has4BScalar_boxed_1917_, v_has8BScalar_boxed_1918_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(lean_object* v_fst_1920_, lean_object* v___x_1921_, lean_object* v_a_1922_, lean_object* v___f_1923_, lean_object* v_fst_1924_, lean_object* v_fst_1925_, lean_object* v_fst_1926_, lean_object* v_snd_1927_, lean_object* v_00___1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = lean_nat_add(v_fst_1920_, v___x_1921_);
v___x_1935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1935_, 0, v_fst_1920_);
lean_ctor_set(v___x_1935_, 1, v_a_1922_);
lean_inc(v___y_1932_);
lean_inc_ref(v___y_1931_);
lean_inc(v___y_1930_);
lean_inc_ref(v___y_1929_);
v___x_1936_ = lean_apply_11(v___f_1923_, v___x_1935_, v___x_1934_, v_fst_1924_, v_fst_1925_, v_fst_1926_, v_snd_1927_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, lean_box(0));
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2___boxed(lean_object* v_fst_1937_, lean_object* v___x_1938_, lean_object* v_a_1939_, lean_object* v___f_1940_, lean_object* v_fst_1941_, lean_object* v_fst_1942_, lean_object* v_fst_1943_, lean_object* v_snd_1944_, lean_object* v_00___1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1937_, v___x_1938_, v_a_1939_, v___f_1940_, v_fst_1941_, v_fst_1942_, v_fst_1943_, v_snd_1944_, v_00___1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___x_1938_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(lean_object* v_a_1954_, lean_object* v_b_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_array_1961_; lean_object* v_start_1962_; lean_object* v_stop_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_2188_; 
v_array_1961_ = lean_ctor_get(v_a_1954_, 0);
v_start_1962_ = lean_ctor_get(v_a_1954_, 1);
v_stop_1963_ = lean_ctor_get(v_a_1954_, 2);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_a_1954_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_1965_ = v_a_1954_;
v_isShared_1966_ = v_isSharedCheck_2188_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_stop_1963_);
lean_inc(v_start_1962_);
lean_inc(v_array_1961_);
lean_dec(v_a_1954_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_2188_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
uint8_t v___x_1967_; 
v___x_1967_ = lean_nat_dec_lt(v_start_1962_, v_stop_1963_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; 
lean_del_object(v___x_1965_);
lean_dec(v_stop_1963_);
lean_dec(v_start_1962_);
lean_dec_ref(v_array_1961_);
v___x_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1968_, 0, v_b_1955_);
return v___x_1968_;
}
else
{
lean_object* v_snd_1969_; lean_object* v_snd_1970_; lean_object* v_snd_1971_; lean_object* v_snd_1972_; lean_object* v_fst_1973_; lean_object* v_fst_1974_; lean_object* v_fst_1975_; lean_object* v_fst_1976_; lean_object* v_fst_1977_; lean_object* v_snd_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
v_snd_1969_ = lean_ctor_get(v_b_1955_, 1);
lean_inc(v_snd_1969_);
v_snd_1970_ = lean_ctor_get(v_snd_1969_, 1);
lean_inc(v_snd_1970_);
v_snd_1971_ = lean_ctor_get(v_snd_1970_, 1);
lean_inc(v_snd_1971_);
v_snd_1972_ = lean_ctor_get(v_snd_1971_, 1);
lean_inc(v_snd_1972_);
v_fst_1973_ = lean_ctor_get(v_b_1955_, 0);
lean_inc(v_fst_1973_);
lean_dec_ref(v_b_1955_);
v_fst_1974_ = lean_ctor_get(v_snd_1969_, 0);
lean_inc(v_fst_1974_);
lean_dec(v_snd_1969_);
v_fst_1975_ = lean_ctor_get(v_snd_1970_, 0);
lean_inc(v_fst_1975_);
lean_dec(v_snd_1970_);
v_fst_1976_ = lean_ctor_get(v_snd_1971_, 0);
lean_inc(v_fst_1976_);
lean_dec(v_snd_1971_);
v_fst_1977_ = lean_ctor_get(v_snd_1972_, 0);
lean_inc(v_fst_1977_);
v_snd_1978_ = lean_ctor_get(v_snd_1972_, 1);
lean_inc(v_snd_1978_);
lean_dec(v_snd_1972_);
v___x_1979_ = lean_unsigned_to_nat(0u);
v___x_1980_ = lean_unsigned_to_nat(1u);
v___x_1981_ = lean_nat_add(v_start_1962_, v___x_1980_);
lean_inc_ref(v_array_1961_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 1, v___x_1981_);
v___x_1983_ = v___x_1965_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_array_1961_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v___x_1981_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_stop_1963_);
v___x_1983_ = v_reuseFailAlloc_2187_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___y_1985_; lean_object* v___x_2005_; lean_object* v___f_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2005_ = lean_array_fget(v_array_1961_, v_start_1962_);
lean_dec(v_start_1962_);
lean_dec_ref(v_array_1961_);
lean_inc(v_fst_1973_);
v___f_2006_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2006_, 0, v_fst_1973_);
v___x_2007_ = l_Lean_Expr_fvarId_x21(v___x_2005_);
lean_dec(v___x_2005_);
v___x_2008_ = l_Lean_FVarId_getType___redArg(v___x_2007_, v___y_1956_, v___y_1958_, v___y_1959_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2010_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
v___x_2010_ = l_Lean_Compiler_LCNF_toLCNFType(v_a_2009_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
v___x_2012_ = l_Lean_Compiler_LCNF_toMonoType(v_a_2011_, v___y_1958_, v___y_1959_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
v___x_2014_ = l_Lean_Compiler_LCNF_toImpureType(v_a_2013_, v___y_1958_, v___y_1959_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
if (lean_obj_tag(v_a_2015_) == 4)
{
lean_object* v_declName_2016_; 
v_declName_2016_ = lean_ctor_get(v_a_2015_, 0);
if (lean_obj_tag(v_declName_2016_) == 1)
{
lean_object* v_pre_2017_; 
v_pre_2017_ = lean_ctor_get(v_declName_2016_, 0);
if (lean_obj_tag(v_pre_2017_) == 0)
{
lean_object* v_us_2018_; lean_object* v_str_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v_us_2018_ = lean_ctor_get(v_a_2015_, 1);
v_str_2019_ = lean_ctor_get(v_declName_2016_, 1);
v___x_2020_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__0));
v___x_2021_ = lean_string_dec_eq(v_str_2019_, v___x_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2022_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__0));
v___x_2023_ = lean_string_dec_eq(v_str_2019_, v___x_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2024_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__10));
v___x_2025_ = lean_string_dec_eq(v_str_2019_, v___x_2024_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__1));
v___x_2027_ = lean_string_dec_eq(v_str_2019_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__4));
v___x_2029_ = lean_string_dec_eq(v_str_2019_, v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; uint8_t v___x_2031_; 
v___x_2030_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__6));
v___x_2031_ = lean_string_dec_eq(v_str_2019_, v___x_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9));
v___x_2033_ = lean_string_dec_eq(v_str_2019_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6));
v___x_2035_ = lean_string_dec_eq(v_str_2019_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3));
v___x_2037_ = lean_string_dec_eq(v_str_2019_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__0));
v___x_2039_ = lean_string_dec_eq(v_str_2019_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2040_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__3));
v___x_2041_ = lean_string_dec_eq(v_str_2019_, v___x_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2042_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__2));
v___x_2043_ = lean_string_dec_eq(v_str_2019_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
lean_dec(v_fst_1973_);
v___x_2044_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v_a_2015_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref_known(v_a_2015_, 2);
v___y_1985_ = v___x_2044_;
goto v___jp_1984_;
}
else
{
lean_inc(v_pre_2017_);
lean_inc(v_us_2018_);
lean_dec_ref_known(v_a_2015_, 2);
if (lean_obj_tag(v_us_2018_) == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; uint8_t v___x_2050_; uint8_t v___x_2051_; lean_object* v___x_2052_; 
lean_dec_ref(v___f_2006_);
lean_dec(v_snd_1978_);
v___x_2045_ = lean_unsigned_to_nat(8u);
v___x_2046_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__20));
v___x_2047_ = l_Lean_Expr_const___override(v___x_2046_, v_us_2018_);
v___x_2048_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2045_);
lean_ctor_set(v___x_2048_, 1, v___x_1979_);
lean_ctor_set(v___x_2048_, 2, v___x_2047_);
v___x_2049_ = lean_unbox(v_fst_1975_);
lean_dec(v_fst_1975_);
v___x_2050_ = lean_unbox(v_fst_1976_);
lean_dec(v_fst_1976_);
v___x_2051_ = lean_unbox(v_fst_1977_);
lean_dec(v_fst_1977_);
v___x_2052_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1973_, v___x_2048_, v_fst_1974_, v___x_2049_, v___x_2050_, v___x_2051_, v___x_2043_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
v___y_1985_ = v___x_2052_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec(v_fst_1973_);
v___x_2053_ = l_Lean_Name_str___override(v_pre_2017_, v___x_2042_);
v___x_2054_ = l_Lean_Expr_const___override(v___x_2053_, v_us_2018_);
v___x_2055_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2054_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref(v___x_2054_);
v___y_1985_ = v___x_2055_;
goto v___jp_1984_;
}
}
}
else
{
lean_inc(v_pre_2017_);
lean_inc(v_us_2018_);
lean_dec_ref_known(v_a_2015_, 2);
if (lean_obj_tag(v_us_2018_) == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; uint8_t v___x_2061_; uint8_t v___x_2062_; lean_object* v___x_2063_; 
lean_dec_ref(v___f_2006_);
lean_dec(v_fst_1977_);
v___x_2056_ = lean_unsigned_to_nat(4u);
v___x_2057_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__17));
v___x_2058_ = l_Lean_Expr_const___override(v___x_2057_, v_us_2018_);
v___x_2059_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2056_);
lean_ctor_set(v___x_2059_, 1, v___x_1979_);
lean_ctor_set(v___x_2059_, 2, v___x_2058_);
v___x_2060_ = lean_unbox(v_fst_1975_);
lean_dec(v_fst_1975_);
v___x_2061_ = lean_unbox(v_fst_1976_);
lean_dec(v_fst_1976_);
v___x_2062_ = lean_unbox(v_snd_1978_);
lean_dec(v_snd_1978_);
v___x_2063_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1973_, v___x_2059_, v_fst_1974_, v___x_2060_, v___x_2061_, v___x_2041_, v___x_2062_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
v___y_1985_ = v___x_2063_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec(v_fst_1973_);
v___x_2064_ = l_Lean_Name_str___override(v_pre_2017_, v___x_2040_);
v___x_2065_ = l_Lean_Expr_const___override(v___x_2064_, v_us_2018_);
v___x_2066_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2065_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref(v___x_2065_);
v___y_1985_ = v___x_2066_;
goto v___jp_1984_;
}
}
}
else
{
lean_inc(v_pre_2017_);
lean_inc(v_us_2018_);
lean_dec_ref_known(v_a_2015_, 2);
if (lean_obj_tag(v_us_2018_) == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; uint8_t v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; 
lean_dec_ref(v___f_2006_);
lean_dec(v_snd_1978_);
v___x_2067_ = lean_unsigned_to_nat(8u);
v___x_2068_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__26));
v___x_2069_ = l_Lean_Expr_const___override(v___x_2068_, v_us_2018_);
v___x_2070_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2067_);
lean_ctor_set(v___x_2070_, 1, v___x_1979_);
lean_ctor_set(v___x_2070_, 2, v___x_2069_);
v___x_2071_ = lean_unbox(v_fst_1975_);
lean_dec(v_fst_1975_);
v___x_2072_ = lean_unbox(v_fst_1976_);
lean_dec(v_fst_1976_);
v___x_2073_ = lean_unbox(v_fst_1977_);
lean_dec(v_fst_1977_);
v___x_2074_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1973_, v___x_2070_, v_fst_1974_, v___x_2071_, v___x_2072_, v___x_2073_, v___x_2039_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
v___y_1985_ = v___x_2074_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec(v_fst_1973_);
v___x_2075_ = l_Lean_Name_str___override(v_pre_2017_, v___x_2038_);
v___x_2076_ = l_Lean_Expr_const___override(v___x_2075_, v_us_2018_);
v___x_2077_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2076_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref(v___x_2076_);
v___y_1985_ = v___x_2077_;
goto v___jp_1984_;
}
}
}
else
{
lean_inc(v_pre_2017_);
lean_inc(v_us_2018_);
lean_dec_ref_known(v_a_2015_, 2);
if (lean_obj_tag(v_us_2018_) == 0)
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; uint8_t v___x_2083_; uint8_t v___x_2084_; lean_object* v___x_2085_; 
lean_dec_ref(v___f_2006_);
lean_dec(v_fst_1977_);
v___x_2078_ = lean_unsigned_to_nat(4u);
v___x_2079_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__4));
v___x_2080_ = l_Lean_Expr_const___override(v___x_2079_, v_us_2018_);
v___x_2081_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2078_);
lean_ctor_set(v___x_2081_, 1, v___x_1979_);
lean_ctor_set(v___x_2081_, 2, v___x_2080_);
v___x_2082_ = lean_unbox(v_fst_1975_);
lean_dec(v_fst_1975_);
v___x_2083_ = lean_unbox(v_fst_1976_);
lean_dec(v_fst_1976_);
v___x_2084_ = lean_unbox(v_snd_1978_);
lean_dec(v_snd_1978_);
v___x_2085_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1973_, v___x_2081_, v_fst_1974_, v___x_2082_, v___x_2083_, v___x_2037_, v___x_2084_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
v___y_1985_ = v___x_2085_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec(v_fst_1973_);
v___x_2086_ = l_Lean_Name_str___override(v_pre_2017_, v___x_2036_);
v___x_2087_ = l_Lean_Expr_const___override(v___x_2086_, v_us_2018_);
v___x_2088_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2087_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref(v___x_2087_);
v___y_1985_ = v___x_2088_;
goto v___jp_1984_;
}
}
}
else
{
lean_inc(v_pre_2017_);
lean_inc(v_us_2018_);
lean_dec_ref_known(v_a_2015_, 2);
if (lean_obj_tag(v_us_2018_) == 0)
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; uint8_t v___x_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; 
lean_dec_ref(v___f_2006_);
lean_dec(v_fst_1976_);
v___x_2089_ = lean_unsigned_to_nat(2u);
v___x_2090_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__7));
v___x_2091_ = l_Lean_Expr_const___override(v___x_2090_, v_us_2018_);
v___x_2092_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2089_);
lean_ctor_set(v___x_2092_, 1, v___x_1979_);
lean_ctor_set(v___x_2092_, 2, v___x_2091_);
v___x_2093_ = lean_unbox(v_fst_1975_);
lean_dec(v_fst_1975_);
v___x_2094_ = lean_unbox(v_fst_1977_);
lean_dec(v_fst_1977_);
v___x_2095_ = lean_unbox(v_snd_1978_);
lean_dec(v_snd_1978_);
v___x_2096_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1973_, v___x_2092_, v_fst_1974_, v___x_2093_, v___x_2035_, v___x_2094_, v___x_2095_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
v___y_1985_ = v___x_2096_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_dec(v_fst_1973_);
v___x_2097_ = l_Lean_Name_str___override(v_pre_2017_, v___x_2034_);
v___x_2098_ = l_Lean_Expr_const___override(v___x_2097_, v_us_2018_);
v___x_2099_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2098_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref(v___x_2098_);
v___y_1985_ = v___x_2099_;
goto v___jp_1984_;
}
}
}
else
{
lean_inc(v_pre_2017_);
lean_inc(v_us_2018_);
lean_dec_ref_known(v_a_2015_, 2);
if (lean_obj_tag(v_us_2018_) == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; uint8_t v___x_2104_; uint8_t v___x_2105_; lean_object* v___x_2106_; 
lean_dec_ref(v___f_2006_);
lean_dec(v_fst_1975_);
v___x_2100_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__10));
v___x_2101_ = l_Lean_Expr_const___override(v___x_2100_, v_us_2018_);
v___x_2102_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2102_, 0, v___x_1980_);
lean_ctor_set(v___x_2102_, 1, v___x_1979_);
lean_ctor_set(v___x_2102_, 2, v___x_2101_);
v___x_2103_ = lean_unbox(v_fst_1976_);
lean_dec(v_fst_1976_);
v___x_2104_ = lean_unbox(v_fst_1977_);
lean_dec(v_fst_1977_);
v___x_2105_ = lean_unbox(v_snd_1978_);
lean_dec(v_snd_1978_);
v___x_2106_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1973_, v___x_2102_, v_fst_1974_, v___x_2033_, v___x_2103_, v___x_2104_, v___x_2105_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
v___y_1985_ = v___x_2106_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_dec(v_fst_1973_);
v___x_2107_ = l_Lean_Name_str___override(v_pre_2017_, v___x_2032_);
v___x_2108_ = l_Lean_Expr_const___override(v___x_2107_, v_us_2018_);
v___x_2109_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2108_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref(v___x_2108_);
v___y_1985_ = v___x_2109_;
goto v___jp_1984_;
}
}
}
else
{
lean_inc(v_pre_2017_);
lean_inc(v_us_2018_);
lean_dec_ref_known(v_a_2015_, 2);
if (lean_obj_tag(v_us_2018_) == 0)
{
lean_object* v___x_2110_; uint8_t v___x_2111_; uint8_t v___x_2112_; uint8_t v___x_2113_; uint8_t v___x_2114_; lean_object* v___x_2115_; 
lean_dec_ref(v___f_2006_);
v___x_2110_ = lean_box(4);
v___x_2111_ = lean_unbox(v_fst_1975_);
lean_dec(v_fst_1975_);
v___x_2112_ = lean_unbox(v_fst_1976_);
lean_dec(v_fst_1976_);
v___x_2113_ = lean_unbox(v_fst_1977_);
lean_dec(v_fst_1977_);
v___x_2114_ = lean_unbox(v_snd_1978_);
lean_dec(v_snd_1978_);
v___x_2115_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1973_, v___x_2110_, v_fst_1974_, v___x_2111_, v___x_2112_, v___x_2113_, v___x_2114_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
v___y_1985_ = v___x_2115_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec(v_fst_1973_);
v___x_2116_ = l_Lean_Name_str___override(v_pre_2017_, v___x_2030_);
v___x_2117_ = l_Lean_Expr_const___override(v___x_2116_, v_us_2018_);
v___x_2118_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2117_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref(v___x_2117_);
v___y_1985_ = v___x_2118_;
goto v___jp_1984_;
}
}
}
else
{
lean_inc(v_pre_2017_);
lean_inc(v_us_2018_);
lean_dec_ref_known(v_a_2015_, 2);
if (lean_obj_tag(v_us_2018_) == 0)
{
lean_object* v___x_2119_; uint8_t v___x_2120_; uint8_t v___x_2121_; uint8_t v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; 
lean_dec_ref(v___f_2006_);
v___x_2119_ = lean_box(0);
v___x_2120_ = lean_unbox(v_fst_1975_);
lean_dec(v_fst_1975_);
v___x_2121_ = lean_unbox(v_fst_1976_);
lean_dec(v_fst_1976_);
v___x_2122_ = lean_unbox(v_fst_1977_);
lean_dec(v_fst_1977_);
v___x_2123_ = lean_unbox(v_snd_1978_);
lean_dec(v_snd_1978_);
v___x_2124_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1973_, v___x_2119_, v_fst_1974_, v___x_2120_, v___x_2121_, v___x_2122_, v___x_2123_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
v___y_1985_ = v___x_2124_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
lean_dec(v_fst_1973_);
v___x_2125_ = l_Lean_Name_str___override(v_pre_2017_, v___x_2028_);
v___x_2126_ = l_Lean_Expr_const___override(v___x_2125_, v_us_2018_);
v___x_2127_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2126_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref(v___x_2126_);
v___y_1985_ = v___x_2127_;
goto v___jp_1984_;
}
}
}
else
{
lean_inc(v_pre_2017_);
lean_inc(v_us_2018_);
lean_dec_ref_known(v_a_2015_, 2);
if (lean_obj_tag(v_us_2018_) == 0)
{
lean_object* v___x_2128_; uint8_t v___x_2129_; uint8_t v___x_2130_; uint8_t v___x_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; 
lean_dec_ref(v___f_2006_);
v___x_2128_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___closed__0));
v___x_2129_ = lean_unbox(v_fst_1975_);
lean_dec(v_fst_1975_);
v___x_2130_ = lean_unbox(v_fst_1976_);
lean_dec(v_fst_1976_);
v___x_2131_ = lean_unbox(v_fst_1977_);
lean_dec(v_fst_1977_);
v___x_2132_ = lean_unbox(v_snd_1978_);
lean_dec(v_snd_1978_);
v___x_2133_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1973_, v___x_2128_, v_fst_1974_, v___x_2129_, v___x_2130_, v___x_2131_, v___x_2132_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
v___y_1985_ = v___x_2133_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec(v_fst_1973_);
v___x_2134_ = l_Lean_Name_str___override(v_pre_2017_, v___x_2026_);
v___x_2135_ = l_Lean_Expr_const___override(v___x_2134_, v_us_2018_);
v___x_2136_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2135_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref(v___x_2135_);
v___y_1985_ = v___x_2136_;
goto v___jp_1984_;
}
}
}
else
{
lean_dec(v_fst_1973_);
if (lean_obj_tag(v_us_2018_) == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = lean_box(0);
v___x_2138_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1974_, v___x_1980_, v_a_2015_, v___f_2006_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2137_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
v___y_1985_ = v___x_2138_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_inc(v_pre_2017_);
lean_inc(v_us_2018_);
lean_dec_ref_known(v_a_2015_, 2);
v___x_2139_ = l_Lean_Name_str___override(v_pre_2017_, v___x_2024_);
v___x_2140_ = l_Lean_Expr_const___override(v___x_2139_, v_us_2018_);
v___x_2141_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2140_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref(v___x_2140_);
v___y_1985_ = v___x_2141_;
goto v___jp_1984_;
}
}
}
else
{
lean_dec(v_fst_1973_);
if (lean_obj_tag(v_us_2018_) == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_box(0);
v___x_2143_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1974_, v___x_1980_, v_a_2015_, v___f_2006_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2142_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
v___y_1985_ = v___x_2143_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_inc(v_pre_2017_);
lean_inc(v_us_2018_);
lean_dec_ref_known(v_a_2015_, 2);
v___x_2144_ = l_Lean_Name_str___override(v_pre_2017_, v___x_2022_);
v___x_2145_ = l_Lean_Expr_const___override(v___x_2144_, v_us_2018_);
v___x_2146_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2145_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref(v___x_2145_);
v___y_1985_ = v___x_2146_;
goto v___jp_1984_;
}
}
}
else
{
lean_dec(v_fst_1973_);
if (lean_obj_tag(v_us_2018_) == 0)
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = lean_box(0);
v___x_2148_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1974_, v___x_1980_, v_a_2015_, v___f_2006_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2147_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
v___y_1985_ = v___x_2148_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_inc(v_pre_2017_);
lean_inc(v_us_2018_);
lean_dec_ref_known(v_a_2015_, 2);
v___x_2149_ = l_Lean_Name_str___override(v_pre_2017_, v___x_2020_);
v___x_2150_ = l_Lean_Expr_const___override(v___x_2149_, v_us_2018_);
v___x_2151_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v___x_2150_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref(v___x_2150_);
v___y_1985_ = v___x_2151_;
goto v___jp_1984_;
}
}
}
else
{
lean_object* v___x_2152_; 
lean_dec(v_fst_1973_);
v___x_2152_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v_a_2015_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref_known(v_a_2015_, 2);
v___y_1985_ = v___x_2152_;
goto v___jp_1984_;
}
}
else
{
lean_object* v___x_2153_; 
lean_dec(v_fst_1973_);
v___x_2153_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v_a_2015_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec_ref_known(v_a_2015_, 2);
v___y_1985_ = v___x_2153_;
goto v___jp_1984_;
}
}
else
{
lean_object* v___x_2154_; 
lean_dec(v_fst_1973_);
v___x_2154_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_2006_, v_fst_1974_, v_fst_1975_, v_fst_1976_, v_fst_1977_, v_snd_1978_, v_a_2015_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v_a_2015_);
v___y_1985_ = v___x_2154_;
goto v___jp_1984_;
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec_ref(v___f_2006_);
lean_dec_ref(v___x_1983_);
lean_dec(v_snd_1978_);
lean_dec(v_fst_1977_);
lean_dec(v_fst_1976_);
lean_dec(v_fst_1975_);
lean_dec(v_fst_1974_);
lean_dec(v_fst_1973_);
v_a_2155_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2014_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2014_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec_ref(v___f_2006_);
lean_dec_ref(v___x_1983_);
lean_dec(v_snd_1978_);
lean_dec(v_fst_1977_);
lean_dec(v_fst_1976_);
lean_dec(v_fst_1975_);
lean_dec(v_fst_1974_);
lean_dec(v_fst_1973_);
v_a_2163_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2012_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2012_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v___f_2006_);
lean_dec_ref(v___x_1983_);
lean_dec(v_snd_1978_);
lean_dec(v_fst_1977_);
lean_dec(v_fst_1976_);
lean_dec(v_fst_1975_);
lean_dec(v_fst_1974_);
lean_dec(v_fst_1973_);
v_a_2171_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2010_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2010_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec_ref(v___f_2006_);
lean_dec_ref(v___x_1983_);
lean_dec(v_snd_1978_);
lean_dec(v_fst_1977_);
lean_dec(v_fst_1976_);
lean_dec(v_fst_1975_);
lean_dec(v_fst_1974_);
lean_dec(v_fst_1973_);
v_a_2179_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2008_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2008_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
v___jp_1984_:
{
if (lean_obj_tag(v___y_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1996_; 
v_a_1986_ = lean_ctor_get(v___y_1985_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___y_1985_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1988_ = v___y_1985_;
v_isShared_1989_ = v_isSharedCheck_1996_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___y_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1996_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
if (lean_obj_tag(v_a_1986_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; 
lean_dec_ref(v___x_1983_);
v_a_1990_ = lean_ctor_get(v_a_1986_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v_a_1986_, 1);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v_a_1990_);
v___x_1992_ = v___x_1988_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
else
{
lean_object* v_a_1994_; 
lean_del_object(v___x_1988_);
v_a_1994_ = lean_ctor_get(v_a_1986_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v_a_1986_, 1);
v_a_1954_ = v___x_1983_;
v_b_1955_ = v_a_1994_;
goto _start;
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref(v___x_1983_);
v_a_1997_ = lean_ctor_get(v___y_1985_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___y_1985_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___y_1985_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___y_1985_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___boxed(lean_object* v_a_2189_, lean_object* v_b_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v_a_2189_, v_b_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
return v_res_2196_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = lean_unsigned_to_nat(1u);
v___x_2198_ = l_Lean_Compiler_LCNF_spillLinkIdx;
v___x_2199_ = lean_nat_add(v___x_2198_, v___x_2197_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1(lean_object* v_ctorName_2200_, lean_object* v_cidx_2201_, lean_object* v_numFields_2202_, lean_object* v_numParams_2203_, uint8_t v___x_2204_, lean_object* v___f_2205_, lean_object* v_params_2206_, lean_object* v_x_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v_fields_2216_; lean_object* v_nextOffset_2217_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2221_ = lean_mk_empty_array_with_capacity(v_numFields_2202_);
v___x_2222_ = lean_unsigned_to_nat(0u);
v___x_2223_ = lean_nat_add(v_numParams_2203_, v_numFields_2202_);
v___x_2224_ = l_Array_toSubarray___redArg(v_params_2206_, v_numParams_2203_, v___x_2223_);
v___x_2225_ = lean_box(v___x_2204_);
v___x_2226_ = lean_box(v___x_2204_);
v___x_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2225_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___x_2228_ = lean_box(v___x_2204_);
v___x_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
lean_ctor_set(v___x_2229_, 1, v___x_2227_);
v___x_2230_ = lean_box(v___x_2204_);
v___x_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
lean_ctor_set(v___x_2231_, 1, v___x_2229_);
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2222_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2221_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v___x_2224_, v___x_2233_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v_snd_2236_; lean_object* v_snd_2237_; lean_object* v_fst_2238_; lean_object* v_fst_2239_; lean_object* v_fst_2240_; lean_object* v_snd_2241_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v_fields_2245_; lean_object* v_nextOffset_2246_; lean_object* v_fst_2252_; lean_object* v_snd_2253_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v_fields_2257_; lean_object* v_nextOffset_2258_; lean_object* v_fst_2264_; lean_object* v_snd_2265_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v_fields_2269_; lean_object* v_nextOffset_2270_; lean_object* v_fields_2277_; lean_object* v_nextIdx_2278_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
v_snd_2236_ = lean_ctor_get(v_a_2235_, 1);
lean_inc(v_snd_2236_);
v_snd_2237_ = lean_ctor_get(v_snd_2236_, 1);
lean_inc(v_snd_2237_);
v_fst_2238_ = lean_ctor_get(v_a_2235_, 0);
lean_inc(v_fst_2238_);
lean_dec(v_a_2235_);
v_fst_2239_ = lean_ctor_get(v_snd_2236_, 0);
lean_inc(v_fst_2239_);
lean_dec(v_snd_2236_);
v_fst_2240_ = lean_ctor_get(v_snd_2237_, 0);
lean_inc(v_fst_2240_);
v_snd_2241_ = lean_ctor_get(v_snd_2237_, 1);
lean_inc(v_snd_2241_);
lean_dec(v_snd_2237_);
v_fst_2252_ = lean_ctor_get(v_snd_2241_, 0);
lean_inc(v_fst_2252_);
v_snd_2253_ = lean_ctor_get(v_snd_2241_, 1);
lean_inc(v_snd_2253_);
lean_dec(v_snd_2241_);
v_fst_2264_ = lean_ctor_get(v_snd_2253_, 0);
lean_inc(v_fst_2264_);
v_snd_2265_ = lean_ctor_get(v_snd_2253_, 1);
lean_inc(v_snd_2265_);
lean_dec(v_snd_2253_);
v___x_2290_ = l_Lean_Compiler_LCNF_numSpillObjs(v_fst_2239_);
v___x_2291_ = lean_nat_dec_lt(v___x_2222_, v___x_2290_);
lean_dec(v___x_2290_);
if (v___x_2291_ == 0)
{
v_fields_2277_ = v_fst_2238_;
v_nextIdx_2278_ = v_fst_2239_;
goto v___jp_2276_;
}
else
{
size_t v_sz_2292_; size_t v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_dec(v_fst_2239_);
v_sz_2292_ = lean_array_size(v_fst_2238_);
v___x_2293_ = ((size_t)0ULL);
v___x_2294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5(v_sz_2292_, v___x_2293_, v_fst_2238_);
v___x_2295_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___closed__0, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___closed__0);
v_fields_2277_ = v___x_2294_;
v_nextIdx_2278_ = v___x_2295_;
goto v___jp_2276_;
}
v___jp_2242_:
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_unbox(v_fst_2240_);
lean_dec(v_fst_2240_);
if (v___x_2247_ == 0)
{
lean_dec_ref(v___f_2205_);
v___y_2214_ = v___y_2243_;
v___y_2215_ = v___y_2244_;
v_fields_2216_ = v_fields_2245_;
v_nextOffset_2217_ = v_nextOffset_2246_;
goto v___jp_2213_;
}
else
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v_fst_2250_; lean_object* v_snd_2251_; 
v___x_2248_ = lean_unsigned_to_nat(1u);
v___x_2249_ = lean_apply_3(v___f_2205_, v_fields_2245_, v___x_2248_, v_nextOffset_2246_);
v_fst_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_fst_2250_);
v_snd_2251_ = lean_ctor_get(v___x_2249_, 1);
lean_inc(v_snd_2251_);
lean_dec_ref(v___x_2249_);
v___y_2214_ = v___y_2243_;
v___y_2215_ = v___y_2244_;
v_fields_2216_ = v_fst_2250_;
v_nextOffset_2217_ = v_snd_2251_;
goto v___jp_2213_;
}
}
v___jp_2254_:
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_unbox(v_fst_2252_);
lean_dec(v_fst_2252_);
if (v___x_2259_ == 0)
{
v___y_2243_ = v___y_2255_;
v___y_2244_ = v___y_2256_;
v_fields_2245_ = v_fields_2257_;
v_nextOffset_2246_ = v_nextOffset_2258_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v_fst_2262_; lean_object* v_snd_2263_; 
v___x_2260_ = lean_unsigned_to_nat(2u);
lean_inc_ref(v___f_2205_);
v___x_2261_ = lean_apply_3(v___f_2205_, v_fields_2257_, v___x_2260_, v_nextOffset_2258_);
v_fst_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_fst_2262_);
v_snd_2263_ = lean_ctor_get(v___x_2261_, 1);
lean_inc(v_snd_2263_);
lean_dec_ref(v___x_2261_);
v___y_2243_ = v___y_2255_;
v___y_2244_ = v___y_2256_;
v_fields_2245_ = v_fst_2262_;
v_nextOffset_2246_ = v_snd_2263_;
goto v___jp_2242_;
}
}
v___jp_2266_:
{
uint8_t v___x_2271_; 
v___x_2271_ = lean_unbox(v_fst_2264_);
lean_dec(v_fst_2264_);
if (v___x_2271_ == 0)
{
v___y_2255_ = v___y_2267_;
v___y_2256_ = v___y_2268_;
v_fields_2257_ = v_fields_2269_;
v_nextOffset_2258_ = v_nextOffset_2270_;
goto v___jp_2254_;
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v_fst_2274_; lean_object* v_snd_2275_; 
v___x_2272_ = lean_unsigned_to_nat(4u);
lean_inc_ref(v___f_2205_);
v___x_2273_ = lean_apply_3(v___f_2205_, v_fields_2269_, v___x_2272_, v_nextOffset_2270_);
v_fst_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_fst_2274_);
v_snd_2275_ = lean_ctor_get(v___x_2273_, 1);
lean_inc(v_snd_2275_);
lean_dec_ref(v___x_2273_);
v___y_2255_ = v___y_2267_;
v___y_2256_ = v___y_2268_;
v_fields_2257_ = v_fst_2274_;
v_nextOffset_2258_ = v_snd_2275_;
goto v___jp_2254_;
}
}
v___jp_2276_:
{
size_t v_sz_2279_; size_t v___x_2280_; lean_object* v___x_2281_; lean_object* v_fst_2282_; lean_object* v_snd_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; 
v_sz_2279_ = lean_array_size(v_fields_2277_);
v___x_2280_ = ((size_t)0ULL);
lean_inc(v_nextIdx_2278_);
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(v_sz_2279_, v___x_2280_, v_fields_2277_, v_nextIdx_2278_);
v_fst_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_fst_2282_);
v_snd_2283_ = lean_ctor_get(v___x_2281_, 1);
lean_inc(v_snd_2283_);
lean_dec_ref(v___x_2281_);
v___x_2284_ = lean_nat_sub(v_snd_2283_, v_nextIdx_2278_);
lean_dec(v_snd_2283_);
v___x_2285_ = lean_unbox(v_snd_2265_);
lean_dec(v_snd_2265_);
if (v___x_2285_ == 0)
{
v___y_2267_ = v___x_2284_;
v___y_2268_ = v_nextIdx_2278_;
v_fields_2269_ = v_fst_2282_;
v_nextOffset_2270_ = v___x_2222_;
goto v___jp_2266_;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v_fst_2288_; lean_object* v_snd_2289_; 
v___x_2286_ = lean_unsigned_to_nat(8u);
lean_inc_ref(v___f_2205_);
v___x_2287_ = lean_apply_3(v___f_2205_, v_fst_2282_, v___x_2286_, v___x_2222_);
v_fst_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_fst_2288_);
v_snd_2289_ = lean_ctor_get(v___x_2287_, 1);
lean_inc(v_snd_2289_);
lean_dec_ref(v___x_2287_);
v___y_2267_ = v___x_2284_;
v___y_2268_ = v_nextIdx_2278_;
v_fields_2269_ = v_fst_2288_;
v_nextOffset_2270_ = v_snd_2289_;
goto v___jp_2266_;
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec_ref(v___f_2205_);
lean_dec(v_cidx_2201_);
lean_dec(v_ctorName_2200_);
v_a_2296_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2234_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2234_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
v___jp_2213_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2218_, 0, v_ctorName_2200_);
lean_ctor_set(v___x_2218_, 1, v_cidx_2201_);
lean_ctor_set(v___x_2218_, 2, v___y_2215_);
lean_ctor_set(v___x_2218_, 3, v___y_2214_);
lean_ctor_set(v___x_2218_, 4, v_nextOffset_2217_);
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v_fields_2216_);
v___x_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___boxed(lean_object* v_ctorName_2304_, lean_object* v_cidx_2305_, lean_object* v_numFields_2306_, lean_object* v_numParams_2307_, lean_object* v___x_2308_, lean_object* v___f_2309_, lean_object* v_params_2310_, lean_object* v_x_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
uint8_t v___x_14479__boxed_2317_; lean_object* v_res_2318_; 
v___x_14479__boxed_2317_ = lean_unbox(v___x_2308_);
v_res_2318_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1(v_ctorName_2304_, v_cidx_2305_, v_numFields_2306_, v_numParams_2307_, v___x_14479__boxed_2317_, v___f_2309_, v_params_2310_, v_x_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec_ref(v_x_2311_);
lean_dec(v_numFields_2306_);
return v_res_2318_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2319_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__2));
v___x_2320_ = lean_unsigned_to_nat(66u);
v___x_2321_ = lean_unsigned_to_nat(227u);
v___x_2322_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0));
v___x_2323_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__0));
v___x_2324_ = l_mkPanicMessageWithDecl(v___x_2323_, v___x_2322_, v___x_2321_, v___x_2320_, v___x_2319_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(lean_object* v_ctorName_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___f_2335_; lean_object* v___x_2336_; lean_object* v_env_2337_; uint8_t v___x_2338_; lean_object* v___x_2339_; 
v___f_2335_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__1));
v___x_2336_ = lean_st_ref_get(v_a_2328_);
v_env_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc_ref(v_env_2337_);
lean_dec(v___x_2336_);
v___x_2338_ = 0;
lean_inc(v_ctorName_2326_);
v___x_2339_ = l_Lean_Environment_find_x3f(v_env_2337_, v_ctorName_2326_, v___x_2338_);
if (lean_obj_tag(v___x_2339_) == 1)
{
lean_object* v_val_2340_; 
v_val_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_val_2340_);
lean_dec_ref_known(v___x_2339_, 1);
if (lean_obj_tag(v_val_2340_) == 6)
{
lean_object* v_val_2341_; lean_object* v_toConstantVal_2342_; lean_object* v_cidx_2343_; lean_object* v_numParams_2344_; lean_object* v_numFields_2345_; lean_object* v_type_2346_; lean_object* v___x_2347_; lean_object* v___f_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v_val_2341_ = lean_ctor_get(v_val_2340_, 0);
lean_inc_ref(v_val_2341_);
lean_dec_ref_known(v_val_2340_, 1);
v_toConstantVal_2342_ = lean_ctor_get(v_val_2341_, 0);
lean_inc_ref(v_toConstantVal_2342_);
v_cidx_2343_ = lean_ctor_get(v_val_2341_, 2);
lean_inc(v_cidx_2343_);
v_numParams_2344_ = lean_ctor_get(v_val_2341_, 3);
lean_inc(v_numParams_2344_);
v_numFields_2345_ = lean_ctor_get(v_val_2341_, 4);
lean_inc(v_numFields_2345_);
lean_dec_ref(v_val_2341_);
v_type_2346_ = lean_ctor_get(v_toConstantVal_2342_, 2);
lean_inc_ref(v_type_2346_);
lean_dec_ref(v_toConstantVal_2342_);
v___x_2347_ = lean_box(v___x_2338_);
v___f_2348_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___boxed), 13, 6);
lean_closure_set(v___f_2348_, 0, v_ctorName_2326_);
lean_closure_set(v___f_2348_, 1, v_cidx_2343_);
lean_closure_set(v___f_2348_, 2, v_numFields_2345_);
lean_closure_set(v___f_2348_, 3, v_numParams_2344_);
lean_closure_set(v___f_2348_, 4, v___x_2347_);
lean_closure_set(v___f_2348_, 5, v___f_2335_);
v___x_2349_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__12);
v___x_2350_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__19, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__19_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__19);
v___x_2351_ = lean_st_mk_ref(v___x_2350_);
v___x_2352_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___redArg(v_type_2346_, v___f_2348_, v___x_2338_, v___x_2338_, v___x_2349_, v___x_2351_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2361_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2361_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2361_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2357_ = lean_st_ref_get(v___x_2351_);
lean_dec(v___x_2351_);
lean_dec(v___x_2357_);
if (v_isShared_2356_ == 0)
{
v___x_2359_ = v___x_2355_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2353_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
else
{
lean_dec(v___x_2351_);
return v___x_2352_;
}
}
else
{
lean_dec(v_val_2340_);
lean_dec(v_ctorName_2326_);
v___y_2331_ = v_a_2327_;
v___y_2332_ = v_a_2328_;
goto v___jp_2330_;
}
}
else
{
lean_dec(v___x_2339_);
lean_dec(v_ctorName_2326_);
v___y_2331_ = v_a_2327_;
v___y_2332_ = v_a_2328_;
goto v___jp_2330_;
}
v___jp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0);
v___x_2334_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(v___x_2333_, v___y_2331_, v___y_2332_);
return v___x_2334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___boxed(lean_object* v_ctorName_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(v_ctorName_2362_, v_a_2363_, v_a_2364_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3(lean_object* v_inst_2367_, lean_object* v_R_2368_, lean_object* v_a_2369_, lean_object* v_b_2370_, lean_object* v_c_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v_a_2369_, v_b_2370_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___boxed(lean_object* v_inst_2378_, lean_object* v_R_2379_, lean_object* v_a_2380_, lean_object* v_b_2381_, lean_object* v_c_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3(v_inst_2378_, v_R_2379_, v_a_2380_, v_b_2381_, v_c_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setCtorLayout(lean_object* v_ctorName_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v___x_2393_; lean_object* v_env_2394_; lean_object* v___x_2395_; lean_object* v_toEnvExtension_2396_; lean_object* v_asyncMode_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; 
v___x_2393_ = lean_st_ref_get(v_a_2391_);
v_env_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc_ref(v_env_2394_);
lean_dec(v___x_2393_);
v___x_2395_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt;
v_toEnvExtension_2396_ = lean_ctor_get(v___x_2395_, 0);
v_asyncMode_2397_ = lean_ctor_get(v_toEnvExtension_2396_, 2);
v___x_2398_ = 0;
lean_inc(v_ctorName_2389_);
v___x_2399_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2395_, v_env_2394_, v_ctorName_2389_, v_asyncMode_2397_, v___x_2398_);
if (lean_obj_tag(v___x_2399_) == 0)
{
uint8_t v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = 0;
lean_inc(v_ctorName_2389_);
v___x_2401_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(v_ctorName_2389_, v_a_2390_, v_a_2391_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2403_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc_n(v_a_2402_, 2);
lean_dec_ref_known(v___x_2401_, 1);
v___x_2403_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout(v_a_2402_, v_a_2390_, v_a_2391_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2432_; 
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; 
v_unused_2433_ = lean_ctor_get(v___x_2403_, 0);
lean_dec(v_unused_2433_);
v___x_2405_ = v___x_2403_;
v_isShared_2406_ = v_isSharedCheck_2432_;
goto v_resetjp_2404_;
}
else
{
lean_dec(v___x_2403_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2432_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v_env_2408_; lean_object* v_nextMacroScope_2409_; lean_object* v_ngen_2410_; lean_object* v_auxDeclNGen_2411_; lean_object* v_traceState_2412_; lean_object* v_recordedDeps_2413_; lean_object* v_messages_2414_; lean_object* v_infoState_2415_; lean_object* v_snapshotTasks_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2430_; 
v___x_2407_ = lean_st_ref_take(v_a_2391_);
v_env_2408_ = lean_ctor_get(v___x_2407_, 0);
v_nextMacroScope_2409_ = lean_ctor_get(v___x_2407_, 1);
v_ngen_2410_ = lean_ctor_get(v___x_2407_, 2);
v_auxDeclNGen_2411_ = lean_ctor_get(v___x_2407_, 3);
v_traceState_2412_ = lean_ctor_get(v___x_2407_, 4);
v_recordedDeps_2413_ = lean_ctor_get(v___x_2407_, 6);
v_messages_2414_ = lean_ctor_get(v___x_2407_, 7);
v_infoState_2415_ = lean_ctor_get(v___x_2407_, 8);
v_snapshotTasks_2416_ = lean_ctor_get(v___x_2407_, 9);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; 
v_unused_2431_ = lean_ctor_get(v___x_2407_, 5);
lean_dec(v_unused_2431_);
v___x_2418_ = v___x_2407_;
v_isShared_2419_ = v_isSharedCheck_2430_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_snapshotTasks_2416_);
lean_inc(v_infoState_2415_);
lean_inc(v_messages_2414_);
lean_inc(v_recordedDeps_2413_);
lean_inc(v_traceState_2412_);
lean_inc(v_auxDeclNGen_2411_);
lean_inc(v_ngen_2410_);
lean_inc(v_nextMacroScope_2409_);
lean_inc(v_env_2408_);
lean_dec(v___x_2407_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2430_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2420_ = lean_box(0);
v___x_2421_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2395_, v_env_2408_, v_ctorName_2389_, v_a_2402_, v___x_2400_);
v___x_2422_ = lean_obj_once(&l_Lean_Compiler_LCNF_setImpureType___closed__1, &l_Lean_Compiler_LCNF_setImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_setImpureType___closed__1);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 5, v___x_2422_);
lean_ctor_set(v___x_2418_, 0, v___x_2421_);
v___x_2424_ = v___x_2418_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v_nextMacroScope_2409_);
lean_ctor_set(v_reuseFailAlloc_2429_, 2, v_ngen_2410_);
lean_ctor_set(v_reuseFailAlloc_2429_, 3, v_auxDeclNGen_2411_);
lean_ctor_set(v_reuseFailAlloc_2429_, 4, v_traceState_2412_);
lean_ctor_set(v_reuseFailAlloc_2429_, 5, v___x_2422_);
lean_ctor_set(v_reuseFailAlloc_2429_, 6, v_recordedDeps_2413_);
lean_ctor_set(v_reuseFailAlloc_2429_, 7, v_messages_2414_);
lean_ctor_set(v_reuseFailAlloc_2429_, 8, v_infoState_2415_);
lean_ctor_set(v_reuseFailAlloc_2429_, 9, v_snapshotTasks_2416_);
v___x_2424_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2425_ = lean_st_ref_put(v_a_2391_, v___x_2424_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2420_);
v___x_2427_ = v___x_2405_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2420_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
else
{
lean_dec(v_a_2402_);
lean_dec(v_ctorName_2389_);
return v___x_2403_;
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec(v_ctorName_2389_);
v_a_2434_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2401_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2401_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v_ctorName_2389_);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2449_ == 0)
{
lean_object* v_unused_2450_; 
v_unused_2450_ = lean_ctor_get(v___x_2399_, 0);
lean_dec(v_unused_2450_);
v___x_2443_ = v___x_2399_;
v_isShared_2444_ = v_isSharedCheck_2449_;
goto v_resetjp_2442_;
}
else
{
lean_dec(v___x_2399_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2449_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2445_ = lean_box(0);
if (v_isShared_2444_ == 0)
{
lean_ctor_set_tag(v___x_2443_, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2445_);
v___x_2447_ = v___x_2443_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setCtorLayout___boxed(lean_object* v_ctorName_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_Compiler_LCNF_setCtorLayout(v_ctorName_2451_, v_a_2452_, v_a_2453_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getCtorLayout(lean_object* v_ctorName_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v___x_2460_; lean_object* v_env_2461_; lean_object* v___x_2462_; lean_object* v_toEnvExtension_2463_; lean_object* v_asyncMode_2464_; uint8_t v___x_2465_; lean_object* v___x_2466_; 
v___x_2460_ = lean_st_ref_get(v_a_2458_);
v_env_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc_ref(v_env_2461_);
lean_dec(v___x_2460_);
v___x_2462_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt;
v_toEnvExtension_2463_ = lean_ctor_get(v___x_2462_, 0);
v_asyncMode_2464_ = lean_ctor_get(v_toEnvExtension_2463_, 2);
v___x_2465_ = 0;
lean_inc(v_ctorName_2456_);
v___x_2466_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2462_, v_env_2461_, v_ctorName_2456_, v_asyncMode_2464_, v___x_2465_);
if (lean_obj_tag(v___x_2466_) == 1)
{
lean_object* v_val_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_ctorName_2456_);
v_val_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_val_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
lean_ctor_set_tag(v___x_2469_, 0);
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_val_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
else
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec(v___x_2466_);
v___x_2475_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__1, &l_Lean_Compiler_LCNF_nameToImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1);
v___x_2476_ = l_Lean_MessageData_ofName(v_ctorName_2456_);
v___x_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2475_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__3, &l_Lean_Compiler_LCNF_nameToImpureType___closed__3_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__3);
v___x_2479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v___x_2479_, v_a_2457_, v_a_2458_);
return v___x_2480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getCtorLayout___boxed(lean_object* v_ctorName_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_2481_, v_a_2482_, v_a_2483_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(lean_object* v_as_2486_, size_t v_sz_2487_, size_t v_i_2488_, lean_object* v_b_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
uint8_t v___x_2493_; 
v___x_2493_ = lean_usize_dec_lt(v_i_2488_, v_sz_2487_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; 
v___x_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2494_, 0, v_b_2489_);
return v___x_2494_;
}
else
{
lean_object* v___x_2495_; lean_object* v_a_2496_; lean_object* v___x_2497_; 
v___x_2495_ = lean_box(0);
v_a_2496_ = lean_array_uget_borrowed(v_as_2486_, v_i_2488_);
lean_inc(v_a_2496_);
v___x_2497_ = l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(v_a_2496_, v___y_2490_, v___y_2491_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v___x_2498_; 
lean_dec_ref_known(v___x_2497_, 1);
lean_inc(v_a_2496_);
v___x_2498_ = l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f(v_a_2496_, v___y_2490_, v___y_2491_);
if (lean_obj_tag(v___x_2498_) == 0)
{
size_t v___x_2499_; size_t v___x_2500_; 
lean_dec_ref_known(v___x_2498_, 1);
v___x_2499_ = ((size_t)1ULL);
v___x_2500_ = lean_usize_add(v_i_2488_, v___x_2499_);
v_i_2488_ = v___x_2500_;
v_b_2489_ = v___x_2495_;
goto _start;
}
else
{
return v___x_2498_;
}
}
else
{
return v___x_2497_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2___boxed(lean_object* v_as_2502_, lean_object* v_sz_2503_, lean_object* v_i_2504_, lean_object* v_b_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
size_t v_sz_boxed_2509_; size_t v_i_boxed_2510_; lean_object* v_res_2511_; 
v_sz_boxed_2509_ = lean_unbox_usize(v_sz_2503_);
lean_dec(v_sz_2503_);
v_i_boxed_2510_ = lean_unbox_usize(v_i_2504_);
lean_dec(v_i_2504_);
v_res_2511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(v_as_2502_, v_sz_boxed_2509_, v_i_boxed_2510_, v_b_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec_ref(v_as_2502_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(uint8_t v_a_2512_, lean_object* v_as_x27_2513_, lean_object* v_b_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
if (lean_obj_tag(v_as_x27_2513_) == 0)
{
lean_object* v___x_2518_; 
v___x_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2518_, 0, v_b_2514_);
return v___x_2518_;
}
else
{
lean_object* v_head_2519_; lean_object* v_tail_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v_head_2519_ = lean_ctor_get(v_as_x27_2513_, 0);
v_tail_2520_ = lean_ctor_get(v_as_x27_2513_, 1);
v___x_2521_ = lean_box(0);
lean_inc(v_head_2519_);
v___x_2522_ = l_Lean_Compiler_LCNF_setOtherDeclMonoType(v_head_2519_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_dec_ref_known(v___x_2522_, 1);
if (v_a_2512_ == 0)
{
lean_object* v___x_2523_; 
lean_inc(v_head_2519_);
v___x_2523_ = l_Lean_Compiler_LCNF_setCtorLayout(v_head_2519_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_dec_ref_known(v___x_2523_, 1);
v_as_x27_2513_ = v_tail_2520_;
v_b_2514_ = v___x_2521_;
goto _start;
}
else
{
return v___x_2523_;
}
}
else
{
v_as_x27_2513_ = v_tail_2520_;
v_b_2514_ = v___x_2521_;
goto _start;
}
}
else
{
return v___x_2522_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg___boxed(lean_object* v_a_2526_, lean_object* v_as_x27_2527_, lean_object* v_b_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
uint8_t v_a_7287__boxed_2532_; lean_object* v_res_2533_; 
v_a_7287__boxed_2532_ = lean_unbox(v_a_2526_);
v_res_2533_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(v_a_7287__boxed_2532_, v_as_x27_2527_, v_b_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v_as_x27_2527_);
return v_res_2533_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_2536_ = l_Lean_stringToMessageData(v___x_2535_);
return v___x_2536_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_2539_ = l_Lean_stringToMessageData(v___x_2538_);
return v___x_2539_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_2542_ = l_Lean_stringToMessageData(v___x_2541_);
return v___x_2542_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_2545_ = l_Lean_stringToMessageData(v___x_2544_);
return v___x_2545_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_2548_ = l_Lean_stringToMessageData(v___x_2547_);
return v___x_2548_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_2551_ = l_Lean_stringToMessageData(v___x_2550_);
return v___x_2551_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_2554_ = l_Lean_stringToMessageData(v___x_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2555_, lean_object* v_declHint_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v_env_2561_; uint8_t v___x_2562_; 
v___x_2559_ = lean_box(0);
v___x_2560_ = lean_st_ref_get(v___y_2557_);
v_env_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc_ref(v_env_2561_);
lean_dec(v___x_2560_);
v___x_2562_ = l_Lean_Name_isAnonymous(v_declHint_2556_);
if (v___x_2562_ == 0)
{
uint8_t v_isExporting_2563_; 
v_isExporting_2563_ = lean_ctor_get_uint8(v_env_2561_, sizeof(void*)*13);
if (v_isExporting_2563_ == 0)
{
lean_object* v___x_2564_; 
lean_dec_ref(v_env_2561_);
lean_dec(v_declHint_2556_);
v___x_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_msg_2555_);
return v___x_2564_;
}
else
{
lean_object* v___x_2565_; uint8_t v___x_2566_; 
lean_inc_ref(v_env_2561_);
v___x_2565_ = l_Lean_Environment_setExporting(v_env_2561_, v___x_2562_);
lean_inc(v_declHint_2556_);
lean_inc_ref(v___x_2565_);
v___x_2566_ = l_Lean_Environment_contains(v___x_2565_, v_declHint_2556_, v_isExporting_2563_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; 
lean_dec_ref(v___x_2565_);
lean_dec_ref(v_env_2561_);
lean_dec(v_declHint_2556_);
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v_msg_2555_);
return v___x_2567_;
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v_c_2573_; lean_object* v___x_2574_; 
v___x_2568_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1);
v___x_2569_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2);
v___x_2570_ = l_Lean_Options_empty;
lean_inc_ref(v___x_2565_);
v___x_2571_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2565_);
lean_ctor_set(v___x_2571_, 1, v___x_2568_);
lean_ctor_set(v___x_2571_, 2, v___x_2569_);
lean_ctor_set(v___x_2571_, 3, v___x_2570_);
lean_inc(v_declHint_2556_);
v___x_2572_ = l_Lean_MessageData_ofConstName(v_declHint_2556_, v___x_2562_);
v_c_2573_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2573_, 0, v___x_2571_);
lean_ctor_set(v_c_2573_, 1, v___x_2572_);
v___x_2574_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_2565_, v_declHint_2556_);
lean_dec_ref(v___x_2565_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_dec_ref(v_env_2561_);
lean_dec(v_declHint_2556_);
v___x_2575_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
lean_ctor_set(v___x_2576_, 1, v_c_2573_);
v___x_2577_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_2578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = l_Lean_MessageData_note(v___x_2578_);
v___x_2580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2580_, 0, v_msg_2555_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
return v___x_2581_;
}
else
{
lean_object* v_val_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2616_; 
v_val_2582_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2584_ = v___x_2574_;
v_isShared_2585_ = v_isSharedCheck_2616_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_val_2582_);
lean_dec(v___x_2574_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2616_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v_moduleNames_2587_; lean_object* v_mod_2588_; uint8_t v___x_2589_; 
v___x_2586_ = l_Lean_Environment_header(v_env_2561_);
lean_dec_ref(v_env_2561_);
v_moduleNames_2587_ = lean_ctor_get(v___x_2586_, 4);
lean_inc_ref(v_moduleNames_2587_);
lean_dec_ref(v___x_2586_);
v_mod_2588_ = lean_array_get(v___x_2559_, v_moduleNames_2587_, v_val_2582_);
lean_dec(v_val_2582_);
lean_dec_ref(v_moduleNames_2587_);
v___x_2589_ = l_Lean_isPrivateName(v_declHint_2556_);
lean_dec(v_declHint_2556_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2590_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_2591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
lean_ctor_set(v___x_2591_, 1, v_c_2573_);
v___x_2592_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_2593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2591_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___x_2594_ = l_Lean_MessageData_ofName(v_mod_2588_);
v___x_2595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2593_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_2597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2595_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = l_Lean_MessageData_note(v___x_2597_);
v___x_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2599_, 0, v_msg_2555_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2599_);
v___x_2601_ = v___x_2584_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2603_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
lean_ctor_set(v___x_2604_, 1, v_c_2573_);
v___x_2605_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_2606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
v___x_2607_ = l_Lean_MessageData_ofName(v_mod_2588_);
v___x_2608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2606_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = l_Lean_MessageData_note(v___x_2610_);
v___x_2612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2612_, 0, v_msg_2555_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2612_);
v___x_2614_ = v___x_2584_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2617_; 
lean_dec_ref(v_env_2561_);
lean_dec(v_declHint_2556_);
v___x_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2617_, 0, v_msg_2555_);
return v___x_2617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2618_, lean_object* v_declHint_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_2618_, v_declHint_2619_, v___y_2620_);
lean_dec(v___y_2620_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(lean_object* v_msg_2623_, lean_object* v_declHint_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v___x_2628_; lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2638_; 
v___x_2628_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_2623_, v_declHint_2624_, v___y_2626_);
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2638_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2638_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2636_; 
v___x_2633_ = l_Lean_unknownIdentifierMessageTag;
v___x_2634_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
lean_ctor_set(v___x_2634_, 1, v_a_2629_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2634_);
v___x_2636_ = v___x_2631_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8___boxed(lean_object* v_msg_2639_, lean_object* v_declHint_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_2639_, v_declHint_2640_, v___y_2641_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(lean_object* v_ref_2645_, lean_object* v_msg_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_toCold_2650_; lean_object* v_currRecDepth_2651_; lean_object* v_ref_2652_; uint16_t v_optionFlags_2653_; uint8_t v_suppressElabErrors_2654_; uint8_t v_checkDeprecated_2655_; uint8_t v_isRecordingDeps_2656_; lean_object* v_ref_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_toCold_2650_ = lean_ctor_get(v___y_2647_, 0);
v_currRecDepth_2651_ = lean_ctor_get(v___y_2647_, 1);
v_ref_2652_ = lean_ctor_get(v___y_2647_, 2);
v_optionFlags_2653_ = lean_ctor_get_uint16(v___y_2647_, sizeof(void*)*3);
v_suppressElabErrors_2654_ = lean_ctor_get_uint8(v___y_2647_, sizeof(void*)*3 + 2);
v_checkDeprecated_2655_ = lean_ctor_get_uint8(v___y_2647_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2656_ = lean_ctor_get_uint8(v___y_2647_, sizeof(void*)*3 + 4);
v_ref_2657_ = l_Lean_replaceRef(v_ref_2645_, v_ref_2652_);
lean_inc(v_currRecDepth_2651_);
lean_inc_ref(v_toCold_2650_);
v___x_2658_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2658_, 0, v_toCold_2650_);
lean_ctor_set(v___x_2658_, 1, v_currRecDepth_2651_);
lean_ctor_set(v___x_2658_, 2, v_ref_2657_);
lean_ctor_set_uint16(v___x_2658_, sizeof(void*)*3, v_optionFlags_2653_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*3 + 2, v_suppressElabErrors_2654_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*3 + 3, v_checkDeprecated_2655_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*3 + 4, v_isRecordingDeps_2656_);
v___x_2659_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_msg_2646_, v___x_2658_, v___y_2648_);
lean_dec_ref_known(v___x_2658_, 3);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2660_, lean_object* v_msg_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_2660_, v_msg_2661_, v___y_2662_, v___y_2663_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v_ref_2660_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(lean_object* v_ref_2666_, lean_object* v_msg_2667_, lean_object* v_declHint_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2672_; lean_object* v_a_2673_; lean_object* v___x_2674_; 
v___x_2672_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_2667_, v_declHint_2668_, v___y_2669_, v___y_2670_);
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref(v___x_2672_);
v___x_2674_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_2666_, v_a_2673_, v___y_2669_, v___y_2670_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2675_, lean_object* v_msg_2676_, lean_object* v_declHint_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_2675_, v_msg_2676_, v_declHint_2677_, v___y_2678_, v___y_2679_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v_ref_2675_);
return v_res_2681_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2684_ = l_Lean_stringToMessageData(v___x_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2685_, lean_object* v_constName_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v___x_2690_; uint8_t v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2690_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2691_ = 0;
lean_inc(v_constName_2686_);
v___x_2692_ = l_Lean_MessageData_ofConstName(v_constName_2686_, v___x_2691_);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2690_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__1, &l_Lean_Compiler_LCNF_nameToImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_2685_, v___x_2695_, v_constName_2686_, v___y_2687_, v___y_2688_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2697_, lean_object* v_constName_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(v_ref_2697_, v_constName_2698_, v___y_2699_, v___y_2700_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v_ref_2697_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(lean_object* v_constName_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_ref_2707_; lean_object* v___x_2708_; 
v_ref_2707_ = lean_ctor_get(v___y_2704_, 2);
v___x_2708_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(v_ref_2707_, v_constName_2703_, v___y_2704_, v___y_2705_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(v_constName_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0(lean_object* v_constName_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; lean_object* v_env_2719_; uint8_t v___x_2720_; lean_object* v___x_2721_; 
v___x_2718_ = lean_st_ref_get(v___y_2716_);
v_env_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc_ref(v_env_2719_);
lean_dec(v___x_2718_);
v___x_2720_ = 0;
lean_inc(v_constName_2714_);
v___x_2721_ = l_Lean_Environment_find_x3f(v_env_2719_, v_constName_2714_, v___x_2720_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(v_constName_2714_, v___y_2715_, v___y_2716_);
return v___x_2722_;
}
else
{
lean_object* v_val_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec(v_constName_2714_);
v_val_2723_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2721_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_val_2723_);
lean_dec(v___x_2721_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set_tag(v___x_2725_, 0);
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_val_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0___boxed(lean_object* v_constName_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0(v_constName_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
return v_res_2735_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2737_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__2));
v___x_2738_ = lean_unsigned_to_nat(49u);
v___x_2739_ = lean_unsigned_to_nat(338u);
v___x_2740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__0));
v___x_2741_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__0));
v___x_2742_ = l_mkPanicMessageWithDecl(v___x_2741_, v___x_2740_, v___x_2739_, v___x_2738_, v___x_2737_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4(lean_object* v_as_2743_, size_t v_sz_2744_, size_t v_i_2745_, lean_object* v_b_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_a_2751_; uint8_t v___x_2755_; 
v___x_2755_ = lean_usize_dec_lt(v_i_2745_, v_sz_2744_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2756_, 0, v_b_2746_);
return v___x_2756_;
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v_a_2760_; lean_object* v___x_2761_; 
v___x_2757_ = lean_box(1);
v___x_2758_ = lean_unsigned_to_nat(0u);
v___x_2759_ = lean_box(0);
v_a_2760_ = lean_array_uget_borrowed(v_as_2743_, v_i_2745_);
lean_inc(v_a_2760_);
v___x_2761_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0(v_a_2760_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
if (lean_obj_tag(v_a_2762_) == 5)
{
lean_object* v_val_2763_; lean_object* v_toConstantVal_2764_; lean_object* v_ctors_2765_; lean_object* v_type_2766_; uint8_t v___x_2767_; uint8_t v___x_2768_; uint8_t v___x_2769_; uint8_t v___x_2770_; lean_object* v___x_2771_; uint64_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v_val_2763_ = lean_ctor_get(v_a_2762_, 0);
lean_inc_ref(v_val_2763_);
lean_dec_ref_known(v_a_2762_, 1);
v_toConstantVal_2764_ = lean_ctor_get(v_val_2763_, 0);
lean_inc_ref(v_toConstantVal_2764_);
v_ctors_2765_ = lean_ctor_get(v_val_2763_, 4);
lean_inc(v_ctors_2765_);
lean_dec_ref(v_val_2763_);
v_type_2766_ = lean_ctor_get(v_toConstantVal_2764_, 2);
lean_inc_ref(v_type_2766_);
lean_dec_ref(v_toConstantVal_2764_);
v___x_2767_ = 0;
v___x_2768_ = 1;
v___x_2769_ = 0;
v___x_2770_ = 2;
v___x_2771_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2771_, 0, v___x_2767_);
lean_ctor_set_uint8(v___x_2771_, 1, v___x_2767_);
lean_ctor_set_uint8(v___x_2771_, 2, v___x_2767_);
lean_ctor_set_uint8(v___x_2771_, 3, v___x_2767_);
lean_ctor_set_uint8(v___x_2771_, 4, v___x_2767_);
lean_ctor_set_uint8(v___x_2771_, 5, v___x_2755_);
lean_ctor_set_uint8(v___x_2771_, 6, v___x_2755_);
lean_ctor_set_uint8(v___x_2771_, 7, v___x_2767_);
lean_ctor_set_uint8(v___x_2771_, 8, v___x_2755_);
lean_ctor_set_uint8(v___x_2771_, 9, v___x_2768_);
lean_ctor_set_uint8(v___x_2771_, 10, v___x_2769_);
lean_ctor_set_uint8(v___x_2771_, 11, v___x_2755_);
lean_ctor_set_uint8(v___x_2771_, 12, v___x_2755_);
lean_ctor_set_uint8(v___x_2771_, 13, v___x_2755_);
lean_ctor_set_uint8(v___x_2771_, 14, v___x_2770_);
lean_ctor_set_uint8(v___x_2771_, 15, v___x_2755_);
lean_ctor_set_uint8(v___x_2771_, 16, v___x_2755_);
lean_ctor_set_uint8(v___x_2771_, 17, v___x_2755_);
lean_ctor_set_uint8(v___x_2771_, 18, v___x_2755_);
lean_ctor_set_uint8(v___x_2771_, 19, v___x_2767_);
v___x_2772_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2771_);
v___x_2773_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2773_, 0, v___x_2771_);
lean_ctor_set_uint64(v___x_2773_, sizeof(void*)*1, v___x_2772_);
v___x_2774_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__10);
v___x_2775_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__11));
v___x_2776_ = lean_box(0);
v___x_2777_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2777_, 0, v___x_2773_);
lean_ctor_set(v___x_2777_, 1, v___x_2757_);
lean_ctor_set(v___x_2777_, 2, v___x_2774_);
lean_ctor_set(v___x_2777_, 3, v___x_2775_);
lean_ctor_set(v___x_2777_, 4, v___x_2776_);
lean_ctor_set(v___x_2777_, 5, v___x_2758_);
lean_ctor_set(v___x_2777_, 6, v___x_2776_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*7, v___x_2767_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*7 + 1, v___x_2767_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*7 + 2, v___x_2767_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*7 + 3, v___x_2755_);
v___x_2778_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__19, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__19_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__4___redArg___closed__19);
v___x_2779_ = lean_st_mk_ref(v___x_2778_);
v___x_2780_ = l_Lean_Meta_isPropFormerType(v_type_2766_, v___x_2777_, v___x_2779_, v___y_2747_, v___y_2748_);
lean_dec_ref_known(v___x_2777_, 7);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2782_; uint8_t v___x_2783_; lean_object* v___x_2784_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2782_ = lean_st_ref_get(v___x_2779_);
lean_dec(v___x_2779_);
lean_dec(v___x_2782_);
v___x_2783_ = lean_unbox(v_a_2781_);
lean_dec(v_a_2781_);
v___x_2784_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(v___x_2783_, v_ctors_2765_, v___x_2759_, v___y_2747_, v___y_2748_);
lean_dec(v_ctors_2765_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_dec_ref_known(v___x_2784_, 1);
v_a_2751_ = v___x_2759_;
goto v___jp_2750_;
}
else
{
return v___x_2784_;
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec(v___x_2779_);
lean_dec(v_ctors_2765_);
v_a_2785_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2780_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2780_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
else
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_dec(v_a_2762_);
v___x_2793_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1);
v___x_2794_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(v___x_2793_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_dec_ref_known(v___x_2794_, 1);
v_a_2751_ = v___x_2759_;
goto v___jp_2750_;
}
else
{
return v___x_2794_;
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
v_a_2795_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2761_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2761_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
v___jp_2750_:
{
size_t v___x_2752_; size_t v___x_2753_; 
v___x_2752_ = ((size_t)1ULL);
v___x_2753_ = lean_usize_add(v_i_2745_, v___x_2752_);
v_i_2745_ = v___x_2753_;
v_b_2746_ = v_a_2751_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___boxed(lean_object* v_as_2803_, lean_object* v_sz_2804_, lean_object* v_i_2805_, lean_object* v_b_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
size_t v_sz_boxed_2810_; size_t v_i_boxed_2811_; lean_object* v_res_2812_; 
v_sz_boxed_2810_ = lean_unbox_usize(v_sz_2804_);
lean_dec(v_sz_2804_);
v_i_boxed_2811_ = lean_unbox_usize(v_i_2805_);
lean_dec(v_i_2805_);
v_res_2812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4(v_as_2803_, v_sz_boxed_2810_, v_i_boxed_2811_, v_b_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v_as_2803_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3(lean_object* v_as_2813_, size_t v_sz_2814_, size_t v_i_2815_, lean_object* v_b_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
uint8_t v___x_2820_; 
v___x_2820_ = lean_usize_dec_lt(v_i_2815_, v_sz_2814_);
if (v___x_2820_ == 0)
{
lean_object* v___x_2821_; 
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v_b_2816_);
return v___x_2821_;
}
else
{
lean_object* v___x_2822_; lean_object* v_a_2823_; lean_object* v___x_2824_; 
v___x_2822_ = lean_box(0);
v_a_2823_ = lean_array_uget_borrowed(v_as_2813_, v_i_2815_);
lean_inc(v_a_2823_);
v___x_2824_ = l_Lean_Compiler_LCNF_setOtherDeclMonoType(v_a_2823_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v___x_2825_; 
lean_dec_ref_known(v___x_2824_, 1);
lean_inc(v_a_2823_);
v___x_2825_ = l_Lean_Compiler_LCNF_setImpureType(v_a_2823_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2825_) == 0)
{
size_t v___x_2826_; size_t v___x_2827_; 
lean_dec_ref_known(v___x_2825_, 1);
v___x_2826_ = ((size_t)1ULL);
v___x_2827_ = lean_usize_add(v_i_2815_, v___x_2826_);
v_i_2815_ = v___x_2827_;
v_b_2816_ = v___x_2822_;
goto _start;
}
else
{
return v___x_2825_;
}
}
else
{
return v___x_2824_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3___boxed(lean_object* v_as_2829_, lean_object* v_sz_2830_, lean_object* v_i_2831_, lean_object* v_b_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
size_t v_sz_boxed_2836_; size_t v_i_boxed_2837_; lean_object* v_res_2838_; 
v_sz_boxed_2836_ = lean_unbox_usize(v_sz_2830_);
lean_dec(v_sz_2830_);
v_i_boxed_2837_ = lean_unbox_usize(v_i_2831_);
lean_dec(v_i_2831_);
v_res_2838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3(v_as_2829_, v_sz_boxed_2836_, v_i_boxed_2837_, v_b_2832_, v___y_2833_, v___y_2834_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec_ref(v_as_2829_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(lean_object* v_as_2839_, size_t v_i_2840_, size_t v_stop_2841_, lean_object* v_b_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_a_2846_; uint8_t v___x_2850_; 
v___x_2850_ = lean_usize_dec_eq(v_i_2840_, v_stop_2841_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v_env_2853_; lean_object* v___x_2854_; 
v___x_2851_ = lean_array_uget_borrowed(v_as_2839_, v_i_2840_);
v___x_2852_ = lean_st_ref_get(v___y_2843_);
v_env_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc_ref(v_env_2853_);
lean_dec(v___x_2852_);
lean_inc(v___x_2851_);
v___x_2854_ = l_Lean_Environment_find_x3f(v_env_2853_, v___x_2851_, v___x_2850_);
if (lean_obj_tag(v___x_2854_) == 1)
{
lean_object* v_val_2855_; 
v_val_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_val_2855_);
lean_dec_ref_known(v___x_2854_, 1);
if (lean_obj_tag(v_val_2855_) == 5)
{
lean_object* v___x_2856_; 
lean_dec_ref_known(v_val_2855_, 1);
lean_inc(v___x_2851_);
v___x_2856_ = lean_array_push(v_b_2842_, v___x_2851_);
v_a_2846_ = v___x_2856_;
goto v___jp_2845_;
}
else
{
lean_dec(v_val_2855_);
v_a_2846_ = v_b_2842_;
goto v___jp_2845_;
}
}
else
{
lean_dec(v___x_2854_);
v_a_2846_ = v_b_2842_;
goto v___jp_2845_;
}
}
else
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2857_, 0, v_b_2842_);
return v___x_2857_;
}
v___jp_2845_:
{
size_t v___x_2847_; size_t v___x_2848_; 
v___x_2847_ = ((size_t)1ULL);
v___x_2848_ = lean_usize_add(v_i_2840_, v___x_2847_);
v_i_2840_ = v___x_2848_;
v_b_2842_ = v_a_2846_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg___boxed(lean_object* v_as_2858_, lean_object* v_i_2859_, lean_object* v_stop_2860_, lean_object* v_b_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
size_t v_i_boxed_2864_; size_t v_stop_boxed_2865_; lean_object* v_res_2866_; 
v_i_boxed_2864_ = lean_unbox_usize(v_i_2859_);
lean_dec(v_i_2859_);
v_stop_boxed_2865_ = lean_unbox_usize(v_stop_2860_);
lean_dec(v_stop_2860_);
v_res_2866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_as_2858_, v_i_boxed_2864_, v_stop_boxed_2865_, v_b_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v_as_2858_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compileInductives(lean_object* v_typeNames_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v_a_2874_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2889_ = lean_unsigned_to_nat(0u);
v___x_2890_ = lean_array_get_size(v_typeNames_2869_);
v___x_2891_ = ((lean_object*)(l_Lean_Compiler_LCNF_compileInductives___closed__0));
v___x_2892_ = lean_nat_dec_lt(v___x_2889_, v___x_2890_);
if (v___x_2892_ == 0)
{
v_a_2874_ = v___x_2891_;
goto v___jp_2873_;
}
else
{
size_t v___x_2893_; size_t v___x_2894_; lean_object* v___x_2895_; 
v___x_2893_ = ((size_t)0ULL);
v___x_2894_ = lean_usize_of_nat(v___x_2890_);
v___x_2895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_typeNames_2869_, v___x_2893_, v___x_2894_, v___x_2891_, v_a_2871_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref_known(v___x_2895_, 1);
v_a_2874_ = v_a_2896_;
goto v___jp_2873_;
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
v_a_2897_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2895_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2895_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
v___jp_2873_:
{
lean_object* v___x_2875_; size_t v_sz_2876_; size_t v___x_2877_; lean_object* v___x_2878_; 
v___x_2875_ = lean_box(0);
v_sz_2876_ = lean_array_size(v_a_2874_);
v___x_2877_ = ((size_t)0ULL);
v___x_2878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(v_a_2874_, v_sz_2876_, v___x_2877_, v___x_2875_, v_a_2870_, v_a_2871_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v___x_2879_; 
lean_dec_ref_known(v___x_2878_, 1);
v___x_2879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3(v_a_2874_, v_sz_2876_, v___x_2877_, v___x_2875_, v_a_2870_, v_a_2871_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v___x_2880_; 
lean_dec_ref_known(v___x_2879_, 1);
v___x_2880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4(v_a_2874_, v_sz_2876_, v___x_2877_, v___x_2875_, v_a_2870_, v_a_2871_);
lean_dec_ref(v_a_2874_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v___x_2880_, 0);
lean_dec(v_unused_2888_);
v___x_2882_ = v___x_2880_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_dec(v___x_2880_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2875_);
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2875_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
else
{
return v___x_2880_;
}
}
else
{
lean_dec_ref(v_a_2874_);
return v___x_2879_;
}
}
else
{
lean_dec_ref(v_a_2874_);
return v___x_2878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compileInductives___boxed(lean_object* v_typeNames_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_Compiler_LCNF_compileInductives(v_typeNames_2905_, v_a_2906_, v_a_2907_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_typeNames_2905_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1(uint8_t v_a_2910_, lean_object* v_as_2911_, lean_object* v_as_x27_2912_, lean_object* v_b_2913_, lean_object* v_a_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(v_a_2910_, v_as_x27_2912_, v_b_2913_, v___y_2915_, v___y_2916_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___boxed(lean_object* v_a_2919_, lean_object* v_as_2920_, lean_object* v_as_x27_2921_, lean_object* v_b_2922_, lean_object* v_a_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
uint8_t v_a_7998__boxed_2927_; lean_object* v_res_2928_; 
v_a_7998__boxed_2927_ = lean_unbox(v_a_2919_);
v_res_2928_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1(v_a_7998__boxed_2927_, v_as_2920_, v_as_x27_2921_, v_b_2922_, v_a_2923_, v___y_2924_, v___y_2925_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v_as_x27_2921_);
lean_dec(v_as_2920_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5(lean_object* v_as_2929_, size_t v_i_2930_, size_t v_stop_2931_, lean_object* v_b_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_as_2929_, v_i_2930_, v_stop_2931_, v_b_2932_, v___y_2934_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___boxed(lean_object* v_as_2937_, lean_object* v_i_2938_, lean_object* v_stop_2939_, lean_object* v_b_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
size_t v_i_boxed_2944_; size_t v_stop_boxed_2945_; lean_object* v_res_2946_; 
v_i_boxed_2944_ = lean_unbox_usize(v_i_2938_);
lean_dec(v_i_2938_);
v_stop_boxed_2945_ = lean_unbox_usize(v_stop_2939_);
lean_dec(v_stop_2939_);
v_res_2946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5(v_as_2937_, v_i_boxed_2944_, v_stop_boxed_2945_, v_b_2940_, v___y_2941_, v___y_2942_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec_ref(v_as_2937_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0(lean_object* v_00_u03b1_2947_, lean_object* v_constName_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(v_constName_2948_, v___y_2949_, v___y_2950_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2953_, lean_object* v_constName_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0(v_00_u03b1_2953_, v_constName_2954_, v___y_2955_, v___y_2956_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2959_, lean_object* v_ref_2960_, lean_object* v_constName_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(v_ref_2960_, v_constName_2961_, v___y_2962_, v___y_2963_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2966_, lean_object* v_ref_2967_, lean_object* v_constName_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1(v_00_u03b1_2966_, v_ref_2967_, v_constName_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v_ref_2967_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b1_2973_, lean_object* v_ref_2974_, lean_object* v_msg_2975_, lean_object* v_declHint_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_2974_, v_msg_2975_, v_declHint_2976_, v___y_2977_, v___y_2978_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___boxed(lean_object* v_00_u03b1_2981_, lean_object* v_ref_2982_, lean_object* v_msg_2983_, lean_object* v_declHint_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7(v_00_u03b1_2981_, v_ref_2982_, v_msg_2983_, v_declHint_2984_, v___y_2985_, v___y_2986_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v_ref_2982_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(lean_object* v_msg_2989_, lean_object* v_declHint_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_2989_, v_declHint_2990_, v___y_2992_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2995_, lean_object* v_declHint_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(v_msg_2995_, v_declHint_2996_, v___y_2997_, v___y_2998_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_3001_, lean_object* v_ref_3002_, lean_object* v_msg_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_3002_, v_msg_3003_, v___y_3004_, v___y_3005_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3008_, lean_object* v_ref_3009_, lean_object* v_msg_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9(v_00_u03b1_3008_, v_ref_3009_, v_msg_3010_, v___y_3011_, v___y_3012_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v_ref_3009_);
return v_res_3014_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Irrelevant(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
lean_object* runtime_initialize_Lean_Runtime(uint8_t builtin);
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
res = runtime_initialize_Lean_Runtime(builtin);
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
l_Lean_Compiler_LCNF_spillLinkIdx = _init_l_Lean_Compiler_LCNF_spillLinkIdx();
lean_mark_persistent(l_Lean_Compiler_LCNF_spillLinkIdx);
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
lean_object* initialize_Lean_Runtime(uint8_t builtin);
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
res = initialize_Lean_Runtime(builtin);
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
