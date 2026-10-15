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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCtorInfo_default;
extern lean_object* l_Lean_maxCtorNumObjs;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_setOtherDeclMonoType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object*, lean_object*, lean_object*);
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
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__21;
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
v___x_56_ = l_Lean_Environment_contains(v___x_55_, v_fst_53_, v___x_54_);
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
lean_object* v___y_106_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_121_ = lean_mk_empty_array_with_capacity(v___x_102_);
v___x_122_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1_spec__1(v___x_121_, v_s_104_);
v___x_123_ = lean_array_get_size(v___x_122_);
v___x_124_ = lean_mk_empty_array_with_capacity(v___x_102_);
v___x_125_ = lean_nat_dec_lt(v___x_102_, v___x_123_);
if (v___x_125_ == 0)
{
lean_dec_ref(v___x_122_);
v___y_106_ = v___x_124_;
goto v___jp_105_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = lean_nat_dec_le(v___x_123_, v___x_123_);
if (v___x_126_ == 0)
{
if (v___x_125_ == 0)
{
lean_dec_ref(v___x_122_);
v___y_106_ = v___x_124_;
goto v___jp_105_;
}
else
{
size_t v___x_127_; size_t v___x_128_; lean_object* v___x_129_; 
v___x_127_ = ((size_t)0ULL);
v___x_128_ = lean_usize_of_nat(v___x_123_);
lean_inc_ref(v_env_103_);
v___x_129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__2(v_env_103_, v___x_122_, v___x_127_, v___x_128_, v___x_124_);
lean_dec_ref(v___x_122_);
v___y_106_ = v___x_129_;
goto v___jp_105_;
}
}
else
{
size_t v___x_130_; size_t v___x_131_; lean_object* v___x_132_; 
v___x_130_ = ((size_t)0ULL);
v___x_131_ = lean_usize_of_nat(v___x_123_);
lean_inc_ref(v_env_103_);
v___x_132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__2(v_env_103_, v___x_122_, v___x_130_, v___x_131_, v___x_124_);
lean_dec_ref(v___x_122_);
v___y_106_ = v___x_132_;
goto v___jp_105_;
}
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
uint8_t v___x_111_; 
v___x_111_ = lean_nat_dec_le(v___x_107_, v___x_107_);
if (v___x_111_ == 0)
{
if (v___x_109_ == 0)
{
lean_object* v___x_112_; 
lean_dec_ref(v_env_103_);
lean_inc_ref(v___x_108_);
v___x_112_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_112_, 0, v___x_108_);
lean_ctor_set(v___x_112_, 1, v___x_108_);
lean_ctor_set(v___x_112_, 2, v___y_106_);
return v___x_112_;
}
else
{
size_t v___x_113_; size_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_113_ = ((size_t)0ULL);
v___x_114_ = lean_usize_of_nat(v___x_107_);
v___x_115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0(v_env_103_, v___y_106_, v___x_113_, v___x_114_, v___x_108_);
lean_inc_ref(v___x_115_);
v___x_116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
lean_ctor_set(v___x_116_, 2, v___y_106_);
return v___x_116_;
}
}
else
{
size_t v___x_117_; size_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = ((size_t)0ULL);
v___x_118_ = lean_usize_of_nat(v___x_107_);
v___x_119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__0(v_env_103_, v___y_106_, v___x_117_, v___x_118_, v___x_108_);
lean_inc_ref(v___x_119_);
v___x_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
lean_ctor_set(v___x_120_, 2, v___y_106_);
return v___x_120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2____boxed(lean_object* v___x_133_, lean_object* v_env_134_, lean_object* v_s_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_(v___x_133_, v_env_134_, v_s_135_);
lean_dec(v_s_135_);
lean_dec(v___x_133_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; lean_object* v___x_180_; 
v___f_176_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_));
v___x_177_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_));
v___x_178_ = lean_box(0);
v___x_179_ = 0;
v___x_180_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_177_, v___x_178_, v___x_179_, v___f_176_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2____boxed(lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2_();
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1(lean_object* v_init_183_, lean_object* v_t_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1_spec__1(v_init_183_, v_t_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1___boxed(lean_object* v_init_186_, lean_object* v_t_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_809789689____hygCtx___hyg_2__spec__1(v_init_186_, v_t_187_);
lean_dec(v_t_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__2(lean_object* v_env_189_, lean_object* v_as_190_, size_t v_i_191_, size_t v_stop_192_, lean_object* v_b_193_){
_start:
{
lean_object* v___y_195_; uint8_t v___x_199_; 
v___x_199_ = lean_usize_dec_eq(v_i_191_, v_stop_192_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v_fst_201_; uint8_t v___x_202_; 
v___x_200_ = lean_array_uget_borrowed(v_as_190_, v_i_191_);
v_fst_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_fst_201_);
lean_inc_ref(v_env_189_);
v___x_202_ = l_Lean_Environment_contains(v_env_189_, v_fst_201_, v___x_199_);
if (v___x_202_ == 0)
{
v___y_195_ = v_b_193_;
goto v___jp_194_;
}
else
{
lean_object* v___x_203_; 
lean_inc(v___x_200_);
v___x_203_ = lean_array_push(v_b_193_, v___x_200_);
v___y_195_ = v___x_203_;
goto v___jp_194_;
}
}
else
{
lean_dec_ref(v_env_189_);
return v_b_193_;
}
v___jp_194_:
{
size_t v___x_196_; size_t v___x_197_; 
v___x_196_ = ((size_t)1ULL);
v___x_197_ = lean_usize_add(v_i_191_, v___x_196_);
v_i_191_ = v___x_197_;
v_b_193_ = v___y_195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_204_, lean_object* v_as_205_, lean_object* v_i_206_, lean_object* v_stop_207_, lean_object* v_b_208_){
_start:
{
size_t v_i_boxed_209_; size_t v_stop_boxed_210_; lean_object* v_res_211_; 
v_i_boxed_209_ = lean_unbox_usize(v_i_206_);
lean_dec(v_i_206_);
v_stop_boxed_210_ = lean_unbox_usize(v_stop_207_);
lean_dec(v_stop_207_);
v_res_211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__2(v_env_204_, v_as_205_, v_i_boxed_209_, v_stop_boxed_210_, v_b_208_);
lean_dec_ref(v_as_205_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_init_212_, lean_object* v_x_213_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
lean_object* v_k_214_; lean_object* v_v_215_; lean_object* v_l_216_; lean_object* v_r_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_k_214_ = lean_ctor_get(v_x_213_, 1);
v_v_215_ = lean_ctor_get(v_x_213_, 2);
v_l_216_ = lean_ctor_get(v_x_213_, 3);
v_r_217_ = lean_ctor_get(v_x_213_, 4);
v___x_218_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1_spec__1(v_init_212_, v_l_216_);
lean_inc(v_v_215_);
lean_inc(v_k_214_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_k_214_);
lean_ctor_set(v___x_219_, 1, v_v_215_);
v___x_220_ = lean_array_push(v___x_218_, v___x_219_);
v_init_212_ = v___x_220_;
v_x_213_ = v_r_217_;
goto _start;
}
else
{
return v_init_212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_init_222_, lean_object* v_x_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1_spec__1(v_init_222_, v_x_223_);
lean_dec(v_x_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0(lean_object* v_env_225_, lean_object* v_as_226_, size_t v_i_227_, size_t v_stop_228_, lean_object* v_b_229_){
_start:
{
lean_object* v___y_231_; uint8_t v___x_235_; 
v___x_235_ = lean_usize_dec_eq(v_i_227_, v_stop_228_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v_fst_237_; uint8_t v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_236_ = lean_array_uget_borrowed(v_as_226_, v_i_227_);
v_fst_237_ = lean_ctor_get(v___x_236_, 0);
v___x_238_ = 1;
lean_inc_ref(v_env_225_);
v___x_239_ = l_Lean_Environment_setExporting(v_env_225_, v___x_238_);
lean_inc(v_fst_237_);
v___x_240_ = l_Lean_Environment_contains(v___x_239_, v_fst_237_, v___x_238_);
if (v___x_240_ == 0)
{
v___y_231_ = v_b_229_;
goto v___jp_230_;
}
else
{
lean_object* v___x_241_; 
lean_inc(v___x_236_);
v___x_241_ = lean_array_push(v_b_229_, v___x_236_);
v___y_231_ = v___x_241_;
goto v___jp_230_;
}
}
else
{
lean_dec_ref(v_env_225_);
return v_b_229_;
}
v___jp_230_:
{
size_t v___x_232_; size_t v___x_233_; 
v___x_232_ = ((size_t)1ULL);
v___x_233_ = lean_usize_add(v_i_227_, v___x_232_);
v_i_227_ = v___x_233_;
v_b_229_ = v___y_231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_242_, lean_object* v_as_243_, lean_object* v_i_244_, lean_object* v_stop_245_, lean_object* v_b_246_){
_start:
{
size_t v_i_boxed_247_; size_t v_stop_boxed_248_; lean_object* v_res_249_; 
v_i_boxed_247_ = lean_unbox_usize(v_i_244_);
lean_dec(v_i_244_);
v_stop_boxed_248_ = lean_unbox_usize(v_stop_245_);
lean_dec(v_stop_245_);
v_res_249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0(v_env_242_, v_as_243_, v_i_boxed_247_, v_stop_boxed_248_, v_b_246_);
lean_dec_ref(v_as_243_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_(lean_object* v___x_250_, lean_object* v_env_251_, lean_object* v_s_252_){
_start:
{
lean_object* v___y_254_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_269_ = lean_mk_empty_array_with_capacity(v___x_250_);
v___x_270_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1_spec__1(v___x_269_, v_s_252_);
v___x_271_ = lean_array_get_size(v___x_270_);
v___x_272_ = lean_mk_empty_array_with_capacity(v___x_250_);
v___x_273_ = lean_nat_dec_lt(v___x_250_, v___x_271_);
if (v___x_273_ == 0)
{
lean_dec_ref(v___x_270_);
v___y_254_ = v___x_272_;
goto v___jp_253_;
}
else
{
uint8_t v___x_274_; 
v___x_274_ = lean_nat_dec_le(v___x_271_, v___x_271_);
if (v___x_274_ == 0)
{
if (v___x_273_ == 0)
{
lean_dec_ref(v___x_270_);
v___y_254_ = v___x_272_;
goto v___jp_253_;
}
else
{
size_t v___x_275_; size_t v___x_276_; lean_object* v___x_277_; 
v___x_275_ = ((size_t)0ULL);
v___x_276_ = lean_usize_of_nat(v___x_271_);
lean_inc_ref(v_env_251_);
v___x_277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__2(v_env_251_, v___x_270_, v___x_275_, v___x_276_, v___x_272_);
lean_dec_ref(v___x_270_);
v___y_254_ = v___x_277_;
goto v___jp_253_;
}
}
else
{
size_t v___x_278_; size_t v___x_279_; lean_object* v___x_280_; 
v___x_278_ = ((size_t)0ULL);
v___x_279_ = lean_usize_of_nat(v___x_271_);
lean_inc_ref(v_env_251_);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__2(v_env_251_, v___x_270_, v___x_278_, v___x_279_, v___x_272_);
lean_dec_ref(v___x_270_);
v___y_254_ = v___x_280_;
goto v___jp_253_;
}
}
v___jp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_255_ = lean_array_get_size(v___y_254_);
v___x_256_ = lean_mk_empty_array_with_capacity(v___x_250_);
v___x_257_ = lean_nat_dec_lt(v___x_250_, v___x_255_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
lean_dec_ref(v_env_251_);
lean_inc_ref(v___x_256_);
v___x_258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
lean_ctor_set(v___x_258_, 2, v___y_254_);
return v___x_258_;
}
else
{
uint8_t v___x_259_; 
v___x_259_ = lean_nat_dec_le(v___x_255_, v___x_255_);
if (v___x_259_ == 0)
{
if (v___x_257_ == 0)
{
lean_object* v___x_260_; 
lean_dec_ref(v_env_251_);
lean_inc_ref(v___x_256_);
v___x_260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_260_, 0, v___x_256_);
lean_ctor_set(v___x_260_, 1, v___x_256_);
lean_ctor_set(v___x_260_, 2, v___y_254_);
return v___x_260_;
}
else
{
size_t v___x_261_; size_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = ((size_t)0ULL);
v___x_262_ = lean_usize_of_nat(v___x_255_);
v___x_263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0(v_env_251_, v___y_254_, v___x_261_, v___x_262_, v___x_256_);
lean_inc_ref(v___x_263_);
v___x_264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
lean_ctor_set(v___x_264_, 2, v___y_254_);
return v___x_264_;
}
}
else
{
size_t v___x_265_; size_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = ((size_t)0ULL);
v___x_266_ = lean_usize_of_nat(v___x_255_);
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__0(v_env_251_, v___y_254_, v___x_265_, v___x_266_, v___x_256_);
lean_inc_ref(v___x_267_);
v___x_268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
lean_ctor_set(v___x_268_, 2, v___y_254_);
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2____boxed(lean_object* v___x_281_, lean_object* v_env_282_, lean_object* v_s_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_(v___x_281_, v_env_282_, v_s_283_);
lean_dec(v_s_283_);
lean_dec(v___x_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; 
v___f_292_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_));
v___x_293_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_));
v___x_294_ = lean_box(0);
v___x_295_ = 0;
v___x_296_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_293_, v___x_294_, v___x_295_, v___f_292_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2____boxed(lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2_();
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1(lean_object* v_init_299_, lean_object* v_t_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1_spec__1(v_init_299_, v_t_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1___boxed(lean_object* v_init_302_, lean_object* v_t_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1487298532____hygCtx___hyg_2__spec__1(v_init_302_, v_t_303_);
lean_dec(v_t_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType(lean_object* v_type_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_314_; 
lean_inc_ref(v_type_308_);
v___x_314_ = l_Lean_Meta_isProp(v_type_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; uint8_t v___x_316_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v___x_316_ = lean_unbox(v_a_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
lean_dec_ref_known(v___x_314_, 1);
lean_inc_ref(v_type_308_);
v___x_317_ = l_Lean_Meta_isTypeFormerType(v_type_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; uint8_t v___x_319_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v___x_319_ = lean_unbox(v_a_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_317_, 1);
v___x_320_ = l_Lean_Meta_whnfD(v_type_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_390_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_390_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_390_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_390_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
if (lean_obj_tag(v_a_321_) == 11)
{
lean_object* v_typeName_325_; 
v_typeName_325_ = lean_ctor_get(v_a_321_, 0);
lean_inc(v_typeName_325_);
if (lean_obj_tag(v_typeName_325_) == 1)
{
lean_object* v_pre_326_; 
v_pre_326_ = lean_ctor_get(v_typeName_325_, 0);
if (lean_obj_tag(v_pre_326_) == 0)
{
lean_object* v_idx_327_; lean_object* v_struct_328_; lean_object* v_str_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_idx_327_ = lean_ctor_get(v_a_321_, 1);
lean_inc(v_idx_327_);
v_struct_328_ = lean_ctor_get(v_a_321_, 2);
lean_inc_ref(v_struct_328_);
lean_dec_ref_known(v_a_321_, 3);
v_str_329_ = lean_ctor_get(v_typeName_325_, 1);
lean_inc_ref(v_str_329_);
lean_dec_ref_known(v_typeName_325_, 2);
v___x_330_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__0));
v___x_331_ = lean_string_dec_eq(v_str_329_, v___x_330_);
lean_dec_ref(v_str_329_);
if (v___x_331_ == 0)
{
lean_object* v___x_333_; 
lean_dec_ref(v_struct_328_);
lean_dec(v_idx_327_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_a_318_);
v___x_333_ = v___x_323_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_318_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
else
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_nat_dec_eq(v_idx_327_, v___x_335_);
lean_dec(v_idx_327_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_339_; 
lean_dec_ref(v_struct_328_);
lean_dec(v_a_318_);
v___x_337_ = lean_box(v___x_336_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_337_);
v___x_339_ = v___x_323_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
else
{
if (lean_obj_tag(v_struct_328_) == 5)
{
lean_object* v_fn_341_; 
v_fn_341_ = lean_ctor_get(v_struct_328_, 0);
lean_inc_ref(v_fn_341_);
lean_dec_ref_known(v_struct_328_, 2);
if (lean_obj_tag(v_fn_341_) == 4)
{
lean_object* v_declName_342_; 
v_declName_342_ = lean_ctor_get(v_fn_341_, 0);
lean_inc(v_declName_342_);
if (lean_obj_tag(v_declName_342_) == 1)
{
lean_object* v_pre_343_; 
v_pre_343_ = lean_ctor_get(v_declName_342_, 0);
lean_inc(v_pre_343_);
if (lean_obj_tag(v_pre_343_) == 1)
{
lean_object* v_pre_344_; 
v_pre_344_ = lean_ctor_get(v_pre_343_, 0);
if (lean_obj_tag(v_pre_344_) == 0)
{
lean_object* v_us_345_; lean_object* v_str_346_; lean_object* v_str_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_us_345_ = lean_ctor_get(v_fn_341_, 1);
lean_inc(v_us_345_);
lean_dec_ref_known(v_fn_341_, 2);
v_str_346_ = lean_ctor_get(v_declName_342_, 1);
lean_inc_ref(v_str_346_);
lean_dec_ref_known(v_declName_342_, 2);
v_str_347_ = lean_ctor_get(v_pre_343_, 1);
lean_inc_ref(v_str_347_);
lean_dec_ref_known(v_pre_343_, 2);
v___x_348_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__1));
v___x_349_ = lean_string_dec_eq(v_str_347_, v___x_348_);
lean_dec_ref(v_str_347_);
if (v___x_349_ == 0)
{
lean_object* v___x_351_; 
lean_dec_ref(v_str_346_);
lean_dec(v_us_345_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_a_318_);
v___x_351_ = v___x_323_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_318_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
else
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___closed__2));
v___x_354_ = lean_string_dec_eq(v_str_346_, v___x_353_);
lean_dec_ref(v_str_346_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_357_; 
lean_dec(v_us_345_);
lean_dec(v_a_318_);
v___x_355_ = lean_box(v___x_354_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_355_);
v___x_357_ = v___x_323_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
else
{
if (lean_obj_tag(v_us_345_) == 0)
{
lean_object* v___x_359_; lean_object* v___x_361_; 
lean_dec(v_a_318_);
v___x_359_ = lean_box(v___x_354_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_359_);
v___x_361_ = v___x_323_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
else
{
lean_object* v___x_364_; 
lean_dec(v_us_345_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_a_318_);
v___x_364_ = v___x_323_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_318_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
else
{
lean_object* v___x_367_; 
lean_dec_ref_known(v_pre_343_, 2);
lean_dec_ref_known(v_declName_342_, 2);
lean_dec_ref_known(v_fn_341_, 2);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_a_318_);
v___x_367_ = v___x_323_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_318_);
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
lean_object* v___x_370_; 
lean_dec(v_pre_343_);
lean_dec_ref_known(v_declName_342_, 2);
lean_dec_ref_known(v_fn_341_, 2);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_a_318_);
v___x_370_ = v___x_323_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_318_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
lean_object* v___x_373_; 
lean_dec_ref_known(v_fn_341_, 2);
lean_dec(v_declName_342_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_a_318_);
v___x_373_ = v___x_323_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_318_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
else
{
lean_object* v___x_376_; 
lean_dec_ref(v_fn_341_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_a_318_);
v___x_376_ = v___x_323_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_318_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
else
{
lean_object* v___x_379_; 
lean_dec_ref(v_struct_328_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_a_318_);
v___x_379_ = v___x_323_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_318_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
else
{
lean_object* v___x_382_; 
lean_dec_ref_known(v_typeName_325_, 2);
lean_dec_ref_known(v_a_321_, 3);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_a_318_);
v___x_382_ = v___x_323_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_318_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
else
{
lean_object* v___x_385_; 
lean_dec(v_typeName_325_);
lean_dec_ref_known(v_a_321_, 3);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_a_318_);
v___x_385_ = v___x_323_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_318_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
else
{
lean_object* v___x_388_; 
lean_dec(v_a_321_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_a_318_);
v___x_388_ = v___x_323_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_318_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec(v_a_318_);
v_a_391_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_320_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_320_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_dec_ref(v_type_308_);
return v___x_317_;
}
}
else
{
lean_dec_ref(v_type_308_);
return v___x_317_;
}
}
else
{
lean_dec_ref(v_type_308_);
return v___x_314_;
}
}
else
{
lean_dec_ref(v_type_308_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType___boxed(lean_object* v_type_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureIrrelevantType(v_type_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f(lean_object* v_declName_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt;
v___x_412_ = ((lean_object*)(l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f___closed__0));
v___x_413_ = l_Lean_Compiler_LCNF_Irrelevant_setHasTrivialStructure_x3f(v___x_411_, v___x_412_, v_declName_407_, v_a_408_, v_a_409_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f___boxed(lean_object* v_declName_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f(v_declName_414_, v_a_415_, v_a_416_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(lean_object* v_declName_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt;
v___x_424_ = l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(v___x_423_, v_declName_419_, v_a_420_, v_a_421_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___boxed(lean_object* v_declName_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_declName_425_, v_a_426_, v_a_427_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
return v_res_429_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_box(0);
v___x_440_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__7));
v___x_441_ = l_Lean_Expr_const___override(v___x_440_, v___x_439_);
return v___x_441_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__8);
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_box(0);
v___x_448_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__11));
v___x_449_ = l_Lean_Expr_const___override(v___x_448_, v___x_447_);
return v___x_449_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
return v___x_451_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_box(0);
v___x_455_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__14));
v___x_456_ = l_Lean_Expr_const___override(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__15);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_box(0);
v___x_462_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__17));
v___x_463_ = l_Lean_Expr_const___override(v___x_462_, v___x_461_);
return v___x_463_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__18);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_box(0);
v___x_469_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__20));
v___x_470_ = l_Lean_Expr_const___override(v___x_469_, v___x_468_);
return v___x_470_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__21);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_box(0);
v___x_476_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__23));
v___x_477_ = l_Lean_Expr_const___override(v___x_476_, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__24);
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_box(0);
v___x_483_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__26));
v___x_484_ = l_Lean_Expr_const___override(v___x_483_, v___x_482_);
return v___x_484_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__27);
v___x_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11);
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(lean_object* v_x_493_){
_start:
{
if (lean_obj_tag(v_x_493_) == 1)
{
lean_object* v_pre_494_; 
v_pre_494_ = lean_ctor_get(v_x_493_, 0);
if (lean_obj_tag(v_pre_494_) == 0)
{
lean_object* v_str_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_str_495_ = lean_ctor_get(v_x_493_, 1);
v___x_496_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9));
v___x_497_ = lean_string_dec_eq(v_str_495_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6));
v___x_499_ = lean_string_dec_eq(v_str_495_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3));
v___x_501_ = lean_string_dec_eq(v_str_495_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__0));
v___x_503_ = lean_string_dec_eq(v_str_495_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__1));
v___x_505_ = lean_string_dec_eq(v_str_495_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__2));
v___x_507_ = lean_string_dec_eq(v_str_495_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__3));
v___x_509_ = lean_string_dec_eq(v_str_495_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__4));
v___x_511_ = lean_string_dec_eq(v_str_495_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__5));
v___x_513_ = lean_string_dec_eq(v_str_495_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__6));
v___x_515_ = lean_string_dec_eq(v_str_495_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
v___x_516_ = lean_box(0);
return v___x_516_;
}
else
{
lean_object* v___x_517_; 
v___x_517_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__9);
return v___x_517_;
}
}
else
{
lean_object* v___x_518_; 
v___x_518_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__13);
return v___x_518_;
}
}
else
{
lean_object* v___x_519_; 
v___x_519_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__16);
return v___x_519_;
}
}
else
{
lean_object* v___x_520_; 
v___x_520_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__19);
return v___x_520_;
}
}
else
{
lean_object* v___x_521_; 
v___x_521_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__22);
return v___x_521_;
}
}
else
{
lean_object* v___x_522_; 
v___x_522_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__25);
return v___x_522_;
}
}
else
{
lean_object* v___x_523_; 
v___x_523_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__28);
return v___x_523_;
}
}
else
{
lean_object* v___x_524_; 
v___x_524_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__29);
return v___x_524_;
}
}
else
{
lean_object* v___x_525_; 
v___x_525_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__30);
return v___x_525_;
}
}
else
{
lean_object* v___x_526_; 
v___x_526_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__31);
return v___x_526_;
}
}
else
{
lean_object* v___x_527_; 
v___x_527_ = lean_box(0);
return v___x_527_;
}
}
else
{
lean_object* v___x_528_; 
v___x_528_ = lean_box(0);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___boxed(lean_object* v_x_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(v_x_529_);
lean_dec(v_x_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(lean_object* v_msg_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___f_536_; lean_object* v___x_5513__overap_537_; lean_object* v___x_538_; 
v___f_536_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0));
v___x_5513__overap_537_ = lean_panic_fn_borrowed(v___f_536_, v_msg_532_);
lean_inc(v___y_534_);
lean_inc_ref(v___y_533_);
v___x_538_ = lean_apply_3(v___x_5513__overap_537_, v___y_533_, v___y_534_, lean_box(0));
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___boxed(lean_object* v_msg_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(v_msg_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0(lean_object* v_k_544_, lean_object* v_b_545_, lean_object* v_c_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_552_; 
lean_inc(v___y_550_);
lean_inc_ref(v___y_549_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
v___x_552_ = lean_apply_7(v_k_544_, v_b_545_, v_c_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, lean_box(0));
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0___boxed(lean_object* v_k_553_, lean_object* v_b_554_, lean_object* v_c_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0(v_k_553_, v_b_554_, v_c_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg(lean_object* v_type_562_, lean_object* v_k_563_, uint8_t v_cleanupAnnotations_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___f_570_; uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___f_570_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_570_, 0, v_k_563_);
v___x_571_ = 0;
v___x_572_ = lean_box(0);
v___x_573_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_571_, v___x_572_, v_type_562_, v___f_570_, v_cleanupAnnotations_564_, v___x_571_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_a_582_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_573_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_573_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___boxed(lean_object* v_type_590_, lean_object* v_k_591_, lean_object* v_cleanupAnnotations_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_598_; lean_object* v_res_599_; 
v_cleanupAnnotations_boxed_598_ = lean_unbox(v_cleanupAnnotations_592_);
v_res_599_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg(v_type_590_, v_k_591_, v_cleanupAnnotations_boxed_598_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2(lean_object* v_00_u03b1_600_, lean_object* v_type_601_, lean_object* v_k_602_, uint8_t v_cleanupAnnotations_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg(v_type_601_, v_k_602_, v_cleanupAnnotations_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___boxed(lean_object* v_00_u03b1_610_, lean_object* v_type_611_, lean_object* v_k_612_, lean_object* v_cleanupAnnotations_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_619_; lean_object* v_res_620_; 
v_cleanupAnnotations_boxed_619_ = lean_unbox(v_cleanupAnnotations_613_);
v_res_620_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2(v_00_u03b1_610_, v_type_611_, v_k_612_, v_cleanupAnnotations_boxed_619_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(lean_object* v_a_624_, lean_object* v_b_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_array_631_; lean_object* v_start_632_; lean_object* v_stop_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_690_; 
v_array_631_ = lean_ctor_get(v_a_624_, 0);
v_start_632_ = lean_ctor_get(v_a_624_, 1);
v_stop_633_ = lean_ctor_get(v_a_624_, 2);
v_isSharedCheck_690_ = !lean_is_exclusive(v_a_624_);
if (v_isSharedCheck_690_ == 0)
{
v___x_635_ = v_a_624_;
v_isShared_636_ = v_isSharedCheck_690_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_stop_633_);
lean_inc(v_start_632_);
lean_inc(v_array_631_);
lean_dec(v_a_624_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_690_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
uint8_t v___x_637_; 
v___x_637_ = lean_nat_dec_lt(v_start_632_, v_stop_633_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_del_object(v___x_635_);
lean_dec(v_stop_633_);
lean_dec(v_start_632_);
lean_dec_ref(v_array_631_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_b_625_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
lean_dec_ref(v_b_625_);
v___x_639_ = lean_box(0);
v___x_640_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___closed__0));
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_nat_add(v_start_632_, v___x_641_);
lean_inc_ref(v_array_631_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v___x_642_);
v___x_644_ = v___x_635_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_array_631_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v_stop_633_);
v___x_644_ = v_reuseFailAlloc_689_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_array_fget(v_array_631_, v_start_632_);
lean_dec(v_start_632_);
lean_dec_ref(v_array_631_);
v___x_646_ = l_Lean_Expr_fvarId_x21(v___x_645_);
lean_dec(v___x_645_);
v___x_647_ = l_Lean_FVarId_getType___redArg(v___x_646_, v___y_626_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
v___x_649_ = l_Lean_Compiler_LCNF_toLCNFType(v_a_648_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_651_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 1);
v___x_651_ = l_Lean_Compiler_LCNF_toMonoType(v_a_650_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_664_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_664_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_664_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_664_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
uint8_t v___x_656_; 
v___x_656_ = l_Lean_Expr_isErased(v_a_652_);
lean_dec(v_a_652_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
lean_dec_ref(v___x_644_);
v___x_657_ = lean_box(v___x_637_);
v___x_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___x_639_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_659_);
v___x_661_ = v___x_654_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
lean_del_object(v___x_654_);
v_a_624_ = v___x_644_;
v_b_625_ = v___x_640_;
goto _start;
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v___x_644_);
v_a_665_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_651_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_651_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v___x_644_);
v_a_673_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_649_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_649_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v___x_644_);
v_a_681_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_647_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_647_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___boxed(lean_object* v_a_691_, lean_object* v_b_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(v_a_691_, v_b_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0(uint8_t v___x_699_, lean_object* v_numParams_700_, lean_object* v___x_701_, lean_object* v_params_702_, lean_object* v_x_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_lower_710_; lean_object* v_upper_711_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = lean_array_get_size(v_params_702_);
v___x_738_ = lean_nat_dec_le(v_numParams_700_, v___x_701_);
if (v___x_738_ == 0)
{
lean_dec(v___x_701_);
v_lower_710_ = v_numParams_700_;
v_upper_711_ = v___x_737_;
goto v___jp_709_;
}
else
{
lean_dec(v_numParams_700_);
v_lower_710_ = v___x_701_;
v_upper_711_ = v___x_737_;
goto v___jp_709_;
}
v___jp_709_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = l_Array_toSubarray___redArg(v_params_702_, v_lower_710_, v_upper_711_);
v___x_713_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg___closed__0));
v___x_714_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(v___x_712_, v___x_713_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_728_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_728_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_728_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_728_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_fst_719_; 
v_fst_719_ = lean_ctor_get(v_a_715_, 0);
lean_inc(v_fst_719_);
lean_dec(v_a_715_);
if (lean_obj_tag(v_fst_719_) == 0)
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = lean_box(v___x_699_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_720_);
v___x_722_ = v___x_717_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
else
{
lean_object* v_val_724_; lean_object* v___x_726_; 
v_val_724_ = lean_ctor_get(v_fst_719_, 0);
lean_inc(v_val_724_);
lean_dec_ref_known(v_fst_719_, 1);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v_val_724_);
v___x_726_ = v___x_717_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_val_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
v_a_729_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_714_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_714_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0___boxed(lean_object* v___x_739_, lean_object* v_numParams_740_, lean_object* v___x_741_, lean_object* v_params_742_, lean_object* v_x_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
uint8_t v___x_6902__boxed_749_; lean_object* v_res_750_; 
v___x_6902__boxed_749_ = lean_unbox(v___x_739_);
v_res_750_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0(v___x_6902__boxed_749_, v_numParams_740_, v___x_741_, v_params_742_, v_x_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec_ref(v_x_743_);
return v_res_750_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_754_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_755_ = lean_unsigned_to_nat(58u);
v___x_756_ = lean_unsigned_to_nat(93u);
v___x_757_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__1));
v___x_758_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_759_ = l_mkPanicMessageWithDecl(v___x_758_, v___x_757_, v___x_756_, v___x_755_, v___x_754_);
return v___x_759_;
}
}
static uint64_t _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_766_; uint64_t v___x_767_; 
v___x_766_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__4));
v___x_767_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__6(void){
_start:
{
uint64_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_uint64_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__5);
v___x_769_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__4));
v___x_770_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set_uint64(v___x_770_, sizeof(void*)*1, v___x_768_);
return v___x_770_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_771_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_unsigned_to_nat(32u);
v___x_775_ = lean_mk_empty_array_with_capacity(v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10(void){
_start:
{
size_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_777_ = ((size_t)5ULL);
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = lean_unsigned_to_nat(32u);
v___x_780_ = lean_mk_empty_array_with_capacity(v___x_779_);
v___x_781_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__9);
v___x_782_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v___x_780_);
lean_ctor_set(v___x_782_, 2, v___x_778_);
lean_ctor_set(v___x_782_, 3, v___x_778_);
lean_ctor_set_usize(v___x_782_, 4, v___x_777_);
return v___x_782_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__11(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_783_ = lean_box(1);
v___x_784_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10);
v___x_785_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8);
v___x_786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v___x_784_);
lean_ctor_set(v___x_786_, 2, v___x_783_);
return v___x_786_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13(void){
_start:
{
uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_789_ = 1;
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_box(0);
v___x_792_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__12));
v___x_793_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__11);
v___x_794_ = lean_box(1);
v___x_795_ = 0;
v___x_796_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__6);
v___x_797_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___x_794_);
lean_ctor_set(v___x_797_, 2, v___x_793_);
lean_ctor_set(v___x_797_, 3, v___x_792_);
lean_ctor_set(v___x_797_, 4, v___x_791_);
lean_ctor_set(v___x_797_, 5, v___x_790_);
lean_ctor_set(v___x_797_, 6, v___x_791_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*7, v___x_795_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*7 + 1, v___x_795_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*7 + 2, v___x_795_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*7 + 3, v___x_789_);
return v___x_797_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__14(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_798_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_799_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8);
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
lean_ctor_set(v___x_801_, 2, v___x_800_);
lean_ctor_set(v___x_801_, 3, v___x_800_);
lean_ctor_set(v___x_801_, 4, v___x_799_);
lean_ctor_set(v___x_801_, 5, v___x_799_);
lean_ctor_set(v___x_801_, 6, v___x_799_);
lean_ctor_set(v___x_801_, 7, v___x_799_);
lean_ctor_set(v___x_801_, 8, v___x_799_);
lean_ctor_set(v___x_801_, 9, v___x_799_);
lean_ctor_set(v___x_801_, 10, v___x_799_);
lean_ctor_set(v___x_801_, 11, v___x_798_);
return v___x_801_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__15(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8);
v___x_803_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
lean_ctor_set(v___x_803_, 2, v___x_802_);
lean_ctor_set(v___x_803_, 3, v___x_802_);
lean_ctor_set(v___x_803_, 4, v___x_802_);
lean_ctor_set(v___x_803_, 5, v___x_802_);
return v___x_803_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__16(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__8);
v___x_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
lean_ctor_set(v___x_805_, 2, v___x_804_);
lean_ctor_set(v___x_805_, 3, v___x_804_);
lean_ctor_set(v___x_805_, 4, v___x_804_);
return v___x_805_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_806_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__16, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__16_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__16);
v___x_807_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10);
v___x_808_ = lean_box(1);
v___x_809_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__15, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__15_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__15);
v___x_810_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__14);
v___x_811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v___x_809_);
lean_ctor_set(v___x_811_, 2, v___x_808_);
lean_ctor_set(v___x_811_, 3, v___x_807_);
lean_ctor_set(v___x_811_, 4, v___x_806_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(lean_object* v___x_812_, lean_object* v_as_x27_813_, lean_object* v_b_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
if (lean_obj_tag(v_as_x27_813_) == 0)
{
lean_object* v___x_818_; 
lean_dec_ref(v___x_812_);
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v_b_814_);
return v___x_818_;
}
else
{
lean_object* v_head_819_; lean_object* v_tail_820_; uint8_t v_a_822_; lean_object* v___y_828_; lean_object* v___y_829_; uint8_t v___x_841_; lean_object* v___x_842_; 
v_head_819_ = lean_ctor_get(v_as_x27_813_, 0);
v_tail_820_ = lean_ctor_get(v_as_x27_813_, 1);
v___x_841_ = 0;
lean_inc(v_head_819_);
lean_inc_ref(v___x_812_);
v___x_842_ = l_Lean_Environment_find_x3f(v___x_812_, v_head_819_, v___x_841_);
if (lean_obj_tag(v___x_842_) == 1)
{
lean_object* v_val_843_; 
v_val_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v___x_842_, 1);
if (lean_obj_tag(v_val_843_) == 6)
{
lean_object* v_val_844_; lean_object* v_toConstantVal_845_; lean_object* v_numParams_846_; lean_object* v_type_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___f_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_val_844_ = lean_ctor_get(v_val_843_, 0);
lean_inc_ref(v_val_844_);
lean_dec_ref_known(v_val_843_, 1);
v_toConstantVal_845_ = lean_ctor_get(v_val_844_, 0);
lean_inc_ref(v_toConstantVal_845_);
v_numParams_846_ = lean_ctor_get(v_val_844_, 3);
lean_inc(v_numParams_846_);
lean_dec_ref(v_val_844_);
v_type_847_ = lean_ctor_get(v_toConstantVal_845_, 2);
lean_inc_ref(v_type_847_);
lean_dec_ref(v_toConstantVal_845_);
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_box(v___x_841_);
v___f_850_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_850_, 0, v___x_849_);
lean_closure_set(v___f_850_, 1, v_numParams_846_);
lean_closure_set(v___f_850_, 2, v___x_848_);
v___x_851_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13);
v___x_852_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17);
v___x_853_ = lean_st_mk_ref(v___x_852_);
v___x_854_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg(v_type_847_, v___f_850_, v___x_841_, v___x_851_, v___x_853_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = lean_st_ref_get(v___x_853_);
lean_dec(v___x_853_);
lean_dec(v___x_856_);
v___x_857_ = lean_unbox(v_a_855_);
lean_dec(v_a_855_);
v_a_822_ = v___x_857_;
goto v___jp_821_;
}
else
{
lean_dec(v___x_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_858_; uint8_t v___x_859_; 
v_a_858_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_854_, 1);
v___x_859_ = lean_unbox(v_a_858_);
lean_dec(v_a_858_);
v_a_822_ = v___x_859_;
goto v___jp_821_;
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_b_814_);
lean_dec_ref(v___x_812_);
v_a_860_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_854_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_854_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
else
{
lean_dec(v_val_843_);
v___y_828_ = v___y_815_;
v___y_829_ = v___y_816_;
goto v___jp_827_;
}
}
else
{
lean_dec(v___x_842_);
v___y_828_ = v___y_815_;
v___y_829_ = v___y_816_;
goto v___jp_827_;
}
v___jp_821_:
{
if (v_a_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_nat_add(v_b_814_, v___x_823_);
lean_dec(v_b_814_);
v_as_x27_813_ = v_tail_820_;
v_b_814_ = v___x_824_;
goto _start;
}
else
{
v_as_x27_813_ = v_tail_820_;
goto _start;
}
}
v___jp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__3);
v___x_831_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(v___x_830_, v___y_828_, v___y_829_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_dec_ref_known(v___x_831_, 1);
v_as_x27_813_ = v_tail_820_;
goto _start;
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_b_814_);
lean_dec_ref(v___x_812_);
v_a_833_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_831_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_831_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___boxed(lean_object* v___x_868_, lean_object* v_as_x27_869_, lean_object* v_b_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(v___x_868_, v_as_x27_869_, v_b_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v_as_x27_869_);
return v_res_874_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = lean_box(0);
v___x_879_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__1));
v___x_880_ = l_Lean_Expr_const___override(v___x_879_, v___x_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType(lean_object* v_name_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(v_name_881_);
if (lean_obj_tag(v___x_888_) == 1)
{
lean_object* v_val_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec(v_name_881_);
v_val_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_val_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 0);
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_val_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
else
{
lean_object* v___x_897_; lean_object* v_env_898_; uint8_t v___x_899_; lean_object* v___x_900_; 
lean_dec(v___x_888_);
v___x_897_ = lean_st_ref_get(v_a_883_);
v_env_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc_ref_n(v_env_898_, 2);
lean_dec(v___x_897_);
v___x_899_ = 0;
v___x_900_ = l_Lean_Environment_find_x3f(v_env_898_, v_name_881_, v___x_899_);
if (lean_obj_tag(v___x_900_) == 1)
{
lean_object* v_val_901_; 
v_val_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_val_901_);
lean_dec_ref_known(v___x_900_, 1);
if (lean_obj_tag(v_val_901_) == 5)
{
lean_object* v_val_902_; lean_object* v_ctors_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_val_902_ = lean_ctor_get(v_val_901_, 0);
lean_inc_ref(v_val_902_);
lean_dec_ref_known(v_val_901_, 1);
v_ctors_903_ = lean_ctor_get(v_val_902_, 4);
lean_inc(v_ctors_903_);
lean_dec_ref(v_val_902_);
v___x_904_ = l_List_lengthTR___redArg(v_ctors_903_);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(v_env_898_, v_ctors_903_, v___x_905_, v_a_882_, v_a_883_);
lean_dec(v_ctors_903_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_925_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_925_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_925_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_925_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
uint8_t v___x_911_; 
v___x_911_ = lean_nat_dec_eq(v_a_907_, v___x_904_);
if (v___x_911_ == 0)
{
uint8_t v___x_912_; 
lean_dec(v___x_904_);
v___x_912_ = lean_nat_dec_eq(v_a_907_, v___x_905_);
lean_dec(v_a_907_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_913_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_913_);
v___x_915_ = v___x_909_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
else
{
lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_917_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_917_);
v___x_919_ = v___x_909_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___x_921_; lean_object* v___x_923_; 
lean_dec(v_a_907_);
v___x_921_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum(v___x_904_);
lean_dec(v___x_904_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_921_);
v___x_923_ = v___x_909_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v___x_904_);
v_a_926_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_906_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_906_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_dec(v_val_901_);
lean_dec_ref(v_env_898_);
goto v___jp_885_;
}
}
else
{
lean_dec(v___x_900_);
lean_dec_ref(v_env_898_);
goto v___jp_885_;
}
}
v___jp_885_:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___boxed(lean_object* v_name_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType(v_name_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1(lean_object* v_inst_939_, lean_object* v_R_940_, lean_object* v_a_941_, lean_object* v_b_942_, lean_object* v_c_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___redArg(v_a_941_, v_b_942_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1___boxed(lean_object* v_inst_950_, lean_object* v_R_951_, lean_object* v_a_952_, lean_object* v_b_953_, lean_object* v_c_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__1(v_inst_950_, v_R_951_, v_a_952_, v_b_953_, v_c_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3(lean_object* v___x_961_, lean_object* v_as_962_, lean_object* v_as_x27_963_, lean_object* v_b_964_, lean_object* v_a_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg(v___x_961_, v_as_x27_963_, v_b_964_, v___y_966_, v___y_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___boxed(lean_object* v___x_970_, lean_object* v_as_971_, lean_object* v_as_x27_972_, lean_object* v_b_973_, lean_object* v_a_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3(v___x_970_, v_as_971_, v_as_x27_972_, v_b_973_, v_a_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v_as_x27_972_);
lean_dec(v_as_971_);
return v_res_978_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setImpureType___closed__0(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_setImpureType___closed__1(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_obj_once(&l_Lean_Compiler_LCNF_setImpureType___closed__0, &l_Lean_Compiler_LCNF_setImpureType___closed__0_once, _init_l_Lean_Compiler_LCNF_setImpureType___closed__0);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setImpureType(lean_object* v_name_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(v_name_983_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v___x_988_; uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v_env_991_; lean_object* v___x_992_; lean_object* v_toEnvExtension_993_; lean_object* v_asyncMode_994_; uint8_t v___x_995_; lean_object* v___x_996_; 
v___x_988_ = l_Lean_instInhabitedExpr;
v___x_989_ = 0;
v___x_990_ = lean_st_ref_get(v_a_985_);
v_env_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc_ref(v_env_991_);
lean_dec(v___x_990_);
v___x_992_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt;
v_toEnvExtension_993_ = lean_ctor_get(v___x_992_, 0);
v_asyncMode_994_ = lean_ctor_get(v_toEnvExtension_993_, 2);
v___x_995_ = 0;
lean_inc(v_name_983_);
v___x_996_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_988_, v___x_992_, v_env_991_, v_name_983_, v_asyncMode_994_, v___x_995_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v___x_997_; 
lean_inc(v_name_983_);
v___x_997_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType(v_name_983_, v_a_984_, v_a_985_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1027_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1027_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1027_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v_env_1003_; lean_object* v_nextMacroScope_1004_; lean_object* v_ngen_1005_; lean_object* v_auxDeclNGen_1006_; lean_object* v_traceState_1007_; lean_object* v_recordedDeps_1008_; lean_object* v_messages_1009_; lean_object* v_infoState_1010_; lean_object* v_snapshotTasks_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1025_; 
v___x_1002_ = lean_st_ref_take(v_a_985_);
v_env_1003_ = lean_ctor_get(v___x_1002_, 0);
v_nextMacroScope_1004_ = lean_ctor_get(v___x_1002_, 1);
v_ngen_1005_ = lean_ctor_get(v___x_1002_, 2);
v_auxDeclNGen_1006_ = lean_ctor_get(v___x_1002_, 3);
v_traceState_1007_ = lean_ctor_get(v___x_1002_, 4);
v_recordedDeps_1008_ = lean_ctor_get(v___x_1002_, 6);
v_messages_1009_ = lean_ctor_get(v___x_1002_, 7);
v_infoState_1010_ = lean_ctor_get(v___x_1002_, 8);
v_snapshotTasks_1011_ = lean_ctor_get(v___x_1002_, 9);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v___x_1002_, 5);
lean_dec(v_unused_1026_);
v___x_1013_ = v___x_1002_;
v_isShared_1014_ = v_isSharedCheck_1025_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_snapshotTasks_1011_);
lean_inc(v_infoState_1010_);
lean_inc(v_messages_1009_);
lean_inc(v_recordedDeps_1008_);
lean_inc(v_traceState_1007_);
lean_inc(v_auxDeclNGen_1006_);
lean_inc(v_ngen_1005_);
lean_inc(v_nextMacroScope_1004_);
lean_inc(v_env_1003_);
lean_dec(v___x_1002_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1025_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_992_, v_env_1003_, v_name_983_, v_a_998_, v___x_989_);
v___x_1017_ = lean_obj_once(&l_Lean_Compiler_LCNF_setImpureType___closed__1, &l_Lean_Compiler_LCNF_setImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_setImpureType___closed__1);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 5, v___x_1017_);
lean_ctor_set(v___x_1013_, 0, v___x_1016_);
v___x_1019_ = v___x_1013_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_nextMacroScope_1004_);
lean_ctor_set(v_reuseFailAlloc_1024_, 2, v_ngen_1005_);
lean_ctor_set(v_reuseFailAlloc_1024_, 3, v_auxDeclNGen_1006_);
lean_ctor_set(v_reuseFailAlloc_1024_, 4, v_traceState_1007_);
lean_ctor_set(v_reuseFailAlloc_1024_, 5, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1024_, 6, v_recordedDeps_1008_);
lean_ctor_set(v_reuseFailAlloc_1024_, 7, v_messages_1009_);
lean_ctor_set(v_reuseFailAlloc_1024_, 8, v_infoState_1010_);
lean_ctor_set(v_reuseFailAlloc_1024_, 9, v_snapshotTasks_1011_);
v___x_1019_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1020_ = lean_st_ref_put(v_a_985_, v___x_1019_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1015_);
v___x_1022_ = v___x_1000_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1015_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v_name_983_);
v_a_1028_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_997_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_997_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
else
{
lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1043_; 
lean_dec(v_name_983_);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v___x_996_, 0);
lean_dec(v_unused_1044_);
v___x_1037_ = v___x_996_;
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
else
{
lean_dec(v___x_996_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = lean_box(0);
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1039_);
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v_name_983_);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v___x_987_, 0);
lean_dec(v_unused_1053_);
v___x_1046_ = v___x_987_;
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
else
{
lean_dec(v___x_987_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1048_ = lean_box(0);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1048_);
v___x_1050_ = v___x_1046_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setImpureType___boxed(lean_object* v_name_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Compiler_LCNF_setImpureType(v_name_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
return v_res_1058_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__7);
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1061_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1062_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0);
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
lean_ctor_set(v___x_1064_, 2, v___x_1063_);
lean_ctor_set(v___x_1064_, 3, v___x_1063_);
lean_ctor_set(v___x_1064_, 4, v___x_1062_);
lean_ctor_set(v___x_1064_, 5, v___x_1062_);
lean_ctor_set(v___x_1064_, 6, v___x_1062_);
lean_ctor_set(v___x_1064_, 7, v___x_1062_);
lean_ctor_set(v___x_1064_, 8, v___x_1062_);
lean_ctor_set(v___x_1064_, 9, v___x_1062_);
lean_ctor_set(v___x_1064_, 10, v___x_1062_);
lean_ctor_set(v___x_1064_, 11, v___x_1061_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1065_ = lean_box(1);
v___x_1066_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__10);
v___x_1067_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__0);
v___x_1068_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v___x_1066_);
lean_ctor_set(v___x_1068_, 2, v___x_1065_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0(lean_object* v_msgData_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v_toCold_1074_; lean_object* v_env_1075_; lean_object* v_options_1076_; uint8_t v___x_1077_; lean_object* v_env_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1073_ = lean_st_ref_get(v___y_1071_);
v_toCold_1074_ = lean_ctor_get(v___y_1070_, 0);
v_env_1075_ = lean_ctor_get(v___x_1073_, 0);
lean_inc_ref(v_env_1075_);
lean_dec(v___x_1073_);
v_options_1076_ = lean_ctor_get(v_toCold_1074_, 2);
v___x_1077_ = 0;
v_env_1078_ = l_Lean_Environment_setRecordingDeps(v_env_1075_, v___x_1077_);
v___x_1079_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1);
v___x_1080_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2);
lean_inc_ref(v_options_1076_);
v___x_1081_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1081_, 0, v_env_1078_);
lean_ctor_set(v___x_1081_, 1, v___x_1079_);
lean_ctor_set(v___x_1081_, 2, v___x_1080_);
lean_ctor_set(v___x_1081_, 3, v_options_1076_);
v___x_1082_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v_msgData_1069_);
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___boxed(lean_object* v_msgData_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0(v_msgData_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(lean_object* v_msg_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_ref_1093_; lean_object* v___x_1094_; lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1103_; 
v_ref_1093_ = lean_ctor_get(v___y_1090_, 2);
v___x_1094_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0(v_msg_1089_, v___y_1090_, v___y_1091_);
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1103_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1103_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
lean_inc(v_ref_1093_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_ref_1093_);
lean_ctor_set(v___x_1099_, 1, v_a_1095_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set_tag(v___x_1097_, 1);
lean_ctor_set(v___x_1097_, 0, v___x_1099_);
v___x_1101_ = v___x_1097_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___boxed(lean_object* v_msg_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_msg_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1108_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l_Lean_Compiler_LCNF_nameToImpureType___closed__0));
v___x_1111_ = l_Lean_stringToMessageData(v___x_1110_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__3(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l_Lean_Compiler_LCNF_nameToImpureType___closed__2));
v___x_1114_ = l_Lean_stringToMessageData(v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_nameToImpureType(lean_object* v_name_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f(v_name_1115_);
if (lean_obj_tag(v___x_1122_) == 1)
{
lean_object* v_val_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec(v_name_1115_);
v_val_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_val_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 0);
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_val_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v_env_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; 
lean_dec(v___x_1122_);
v___x_1131_ = l_Lean_instInhabitedExpr;
v___x_1132_ = lean_st_ref_get(v_a_1117_);
v_env_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc_ref(v_env_1133_);
lean_dec(v___x_1132_);
v___x_1134_ = 0;
lean_inc(v_name_1115_);
v___x_1135_ = l_Lean_Environment_find_x3f(v_env_1133_, v_name_1115_, v___x_1134_);
if (lean_obj_tag(v___x_1135_) == 1)
{
lean_object* v_val_1136_; 
v_val_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_val_1136_);
lean_dec_ref_known(v___x_1135_, 1);
if (lean_obj_tag(v_val_1136_) == 5)
{
lean_object* v___x_1137_; lean_object* v_env_1138_; lean_object* v___x_1139_; lean_object* v_toEnvExtension_1140_; lean_object* v_asyncMode_1141_; uint8_t v___x_1142_; lean_object* v___x_1143_; 
lean_dec_ref_known(v_val_1136_, 1);
v___x_1137_ = lean_st_ref_get(v_a_1117_);
v_env_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc_ref(v_env_1138_);
lean_dec(v___x_1137_);
v___x_1139_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt;
v_toEnvExtension_1140_ = lean_ctor_get(v___x_1139_, 0);
v_asyncMode_1141_ = lean_ctor_get(v_toEnvExtension_1140_, 2);
v___x_1142_ = 0;
lean_inc(v_name_1115_);
v___x_1143_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1131_, v___x_1139_, v_env_1138_, v_name_1115_, v_asyncMode_1141_, v___x_1142_);
if (lean_obj_tag(v___x_1143_) == 1)
{
lean_object* v_val_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_name_1115_);
v_val_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_val_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set_tag(v___x_1146_, 0);
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_val_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec(v___x_1143_);
v___x_1152_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__1, &l_Lean_Compiler_LCNF_nameToImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1);
v___x_1153_ = l_Lean_MessageData_ofName(v_name_1115_);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__3, &l_Lean_Compiler_LCNF_nameToImpureType___closed__3_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__3);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v___x_1156_, v_a_1116_, v_a_1117_);
return v___x_1157_;
}
}
else
{
lean_dec(v_val_1136_);
lean_dec(v_name_1115_);
goto v___jp_1119_;
}
}
else
{
lean_dec(v___x_1135_);
lean_dec(v_name_1115_);
goto v___jp_1119_;
}
}
v___jp_1119_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_nameToImpureType___boxed(lean_object* v_name_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Compiler_LCNF_nameToImpureType(v_name_1158_, v_a_1159_, v_a_1160_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0(lean_object* v_00_u03b1_1163_, lean_object* v_msg_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_msg_1164_, v___y_1165_, v___y_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___boxed(lean_object* v_00_u03b1_1169_, lean_object* v_msg_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0(v_00_u03b1_1169_, v_msg_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
return v_res_1174_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(lean_object* v_type_1176_){
_start:
{
switch(lean_obj_tag(v_type_1176_))
{
case 4:
{
lean_object* v_declName_1177_; 
v_declName_1177_ = lean_ctor_get(v_type_1176_, 0);
if (lean_obj_tag(v_declName_1177_) == 1)
{
lean_object* v_pre_1178_; 
v_pre_1178_ = lean_ctor_get(v_declName_1177_, 0);
if (lean_obj_tag(v_pre_1178_) == 0)
{
lean_object* v_str_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_str_1179_ = lean_ctor_get(v_declName_1177_, 1);
v___x_1180_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___closed__0));
v___x_1181_ = lean_string_dec_eq(v_str_1179_, v___x_1180_);
return v___x_1181_;
}
else
{
uint8_t v___x_1182_; 
v___x_1182_ = 0;
return v___x_1182_;
}
}
else
{
uint8_t v___x_1183_; 
v___x_1183_ = 0;
return v___x_1183_;
}
}
case 7:
{
lean_object* v_body_1184_; 
v_body_1184_ = lean_ctor_get(v_type_1176_, 2);
v_type_1176_ = v_body_1184_;
goto _start;
}
default: 
{
uint8_t v___x_1186_; 
v___x_1186_ = 0;
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___boxed(lean_object* v_type_1187_){
_start:
{
uint8_t v_res_1188_; lean_object* v_r_1189_; 
v_res_1188_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(v_type_1187_);
lean_dec_ref(v_type_1187_);
v_r_1189_ = lean_box(v_res_1188_);
return v_r_1189_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(lean_object* v_msg_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___f_1194_; lean_object* v___x_747__overap_1195_; lean_object* v___x_1196_; 
v___f_1194_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0));
v___x_747__overap_1195_ = lean_panic_fn_borrowed(v___f_1194_, v_msg_1190_);
lean_inc(v___y_1192_);
lean_inc_ref(v___y_1191_);
v___x_1196_ = lean_apply_3(v___x_747__overap_1195_, v___y_1191_, v___y_1192_, lean_box(0));
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1___boxed(lean_object* v_msg_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(v_msg_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1201_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toImpureType___closed__1(void){
_start:
{
lean_object* v___x_1204_; lean_object* v_dummy_1205_; 
v___x_1204_ = lean_box(0);
v_dummy_1205_ = l_Lean_Expr_sort___override(v___x_1204_);
return v_dummy_1205_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toImpureType___closed__3(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1207_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_1208_ = lean_unsigned_to_nat(41u);
v___x_1209_ = lean_unsigned_to_nat(139u);
v___x_1210_ = ((lean_object*)(l_Lean_Compiler_LCNF_toImpureType___closed__2));
v___x_1211_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_1212_ = l_mkPanicMessageWithDecl(v___x_1211_, v___x_1210_, v___x_1209_, v___x_1208_, v___x_1207_);
return v___x_1212_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toImpureType___closed__4(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1213_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_1214_ = lean_unsigned_to_nat(9u);
v___x_1215_ = lean_unsigned_to_nat(151u);
v___x_1216_ = ((lean_object*)(l_Lean_Compiler_LCNF_toImpureType___closed__2));
v___x_1217_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_1218_ = l_mkPanicMessageWithDecl(v___x_1217_, v___x_1216_, v___x_1215_, v___x_1214_, v___x_1213_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpureType(lean_object* v_type_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
switch(lean_obj_tag(v_type_1219_))
{
case 4:
{
lean_object* v_declName_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_declName_1223_ = lean_ctor_get(v_type_1219_, 0);
lean_inc(v_declName_1223_);
lean_dec_ref_known(v_type_1219_, 2);
v___x_1224_ = ((lean_object*)(l_Lean_Compiler_LCNF_toImpureType___closed__0));
v___x_1225_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(v_declName_1223_, v___x_1224_, v_a_1220_, v_a_1221_);
return v___x_1225_;
}
case 5:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Expr_getAppFn(v_type_1219_);
if (lean_obj_tag(v___x_1226_) == 4)
{
lean_object* v_declName_1227_; lean_object* v_dummy_1228_; lean_object* v_nargs_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_declName_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_declName_1227_);
lean_dec_ref_known(v___x_1226_, 2);
v_dummy_1228_ = lean_obj_once(&l_Lean_Compiler_LCNF_toImpureType___closed__1, &l_Lean_Compiler_LCNF_toImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_toImpureType___closed__1);
v_nargs_1229_ = l_Lean_Expr_getAppNumArgs(v_type_1219_);
lean_inc(v_nargs_1229_);
v___x_1230_ = lean_mk_array(v_nargs_1229_, v_dummy_1228_);
v___x_1231_ = lean_unsigned_to_nat(1u);
v___x_1232_ = lean_nat_sub(v_nargs_1229_, v___x_1231_);
lean_dec(v_nargs_1229_);
v___x_1233_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_type_1219_, v___x_1230_, v___x_1232_);
v___x_1234_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(v_declName_1227_, v___x_1233_, v_a_1220_, v_a_1221_);
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec_ref_known(v_type_1219_, 2);
lean_dec_ref(v___x_1226_);
v___x_1235_ = lean_obj_once(&l_Lean_Compiler_LCNF_toImpureType___closed__3, &l_Lean_Compiler_LCNF_toImpureType___closed__3_once, _init_l_Lean_Compiler_LCNF_toImpureType___closed__3);
v___x_1236_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(v___x_1235_, v_a_1220_, v_a_1221_);
return v___x_1236_;
}
}
case 7:
{
lean_object* v_body_1237_; uint8_t v___x_1238_; 
v_body_1237_ = lean_ctor_get(v_type_1219_, 2);
lean_inc_ref(v_body_1237_);
lean_dec_ref_known(v_type_1219_, 3);
v___x_1238_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(v_body_1237_);
lean_dec_ref(v_body_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__2);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__12);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
}
case 10:
{
lean_object* v_expr_1243_; 
v_expr_1243_ = lean_ctor_get(v_type_1219_, 1);
lean_inc_ref(v_expr_1243_);
lean_dec_ref_known(v_type_1219_, 2);
v_type_1219_ = v_expr_1243_;
goto _start;
}
default: 
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec_ref(v_type_1219_);
v___x_1245_ = lean_obj_once(&l_Lean_Compiler_LCNF_toImpureType___closed__4, &l_Lean_Compiler_LCNF_toImpureType___closed__4_once, _init_l_Lean_Compiler_LCNF_toImpureType___closed__4);
v___x_1246_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(v___x_1245_, v_a_1220_, v_a_1221_);
return v___x_1246_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(lean_object* v_declName_1247_, lean_object* v_args_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = l_Lean_instInhabitedExpr;
lean_inc(v_declName_1247_);
v___x_1253_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_declName_1247_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
if (lean_obj_tag(v_a_1254_) == 1)
{
lean_object* v_val_1255_; lean_object* v_ctorName_1256_; lean_object* v_numParams_1257_; lean_object* v_fieldIdx_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec(v_declName_1247_);
v_val_1255_ = lean_ctor_get(v_a_1254_, 0);
lean_inc(v_val_1255_);
lean_dec_ref_known(v_a_1254_, 1);
v_ctorName_1256_ = lean_ctor_get(v_val_1255_, 0);
lean_inc(v_ctorName_1256_);
v_numParams_1257_ = lean_ctor_get(v_val_1255_, 1);
lean_inc(v_numParams_1257_);
v_fieldIdx_1258_ = lean_ctor_get(v_val_1255_, 2);
lean_inc(v_fieldIdx_1258_);
lean_dec(v_val_1255_);
v___x_1259_ = lean_box(0);
v___x_1260_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(v_ctorName_1256_, v___x_1259_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = l_Array_toSubarray___redArg(v_args_1248_, v___x_1262_, v_numParams_1257_);
v___x_1264_ = l_Subarray_copy___redArg(v___x_1263_);
v___x_1265_ = l_Lean_Compiler_LCNF_instantiateForall(v_a_1261_, v___x_1264_, v_a_1249_, v_a_1250_);
lean_dec_ref(v___x_1264_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = l_Lean_Compiler_LCNF_getParamTypes(v_a_1266_);
v___x_1268_ = lean_array_get(v___x_1252_, v___x_1267_, v_fieldIdx_1258_);
lean_dec(v_fieldIdx_1258_);
lean_dec_ref(v___x_1267_);
v___x_1269_ = l_Lean_Compiler_LCNF_toMonoType(v___x_1268_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = l_Lean_Compiler_LCNF_toImpureType(v_a_1270_, v_a_1249_, v_a_1250_);
return v___x_1271_;
}
else
{
return v___x_1269_;
}
}
else
{
lean_dec(v_fieldIdx_1258_);
return v___x_1265_;
}
}
else
{
lean_dec(v_fieldIdx_1258_);
lean_dec(v_numParams_1257_);
lean_dec_ref(v_args_1248_);
return v___x_1260_;
}
}
else
{
lean_object* v___x_1272_; 
lean_dec(v_a_1254_);
lean_dec_ref(v_args_1248_);
v___x_1272_ = l_Lean_Compiler_LCNF_nameToImpureType(v_declName_1247_, v_a_1249_, v_a_1250_);
return v___x_1272_;
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v_args_1248_);
lean_dec(v_declName_1247_);
v_a_1273_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1253_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1253_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp___boxed(lean_object* v_declName_1281_, lean_object* v_args_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(v_declName_1281_, v_args_1282_, v_a_1283_, v_a_1284_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpureType___boxed(lean_object* v_type_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1287_, v_a_1288_, v_a_1289_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx___impl(lean_object* v_x_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_obj_tag_nat(v_x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx___impl___boxed(lean_object* v_x_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx___impl(v_x_1294_);
lean_dec(v_x_1294_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(lean_object* v_t_1296_, lean_object* v_k_1297_){
_start:
{
switch(lean_obj_tag(v_t_1296_))
{
case 1:
{
lean_object* v_i_1298_; lean_object* v_type_1299_; lean_object* v___x_1300_; 
v_i_1298_ = lean_ctor_get(v_t_1296_, 0);
lean_inc(v_i_1298_);
v_type_1299_ = lean_ctor_get(v_t_1296_, 1);
lean_inc_ref(v_type_1299_);
lean_dec_ref_known(v_t_1296_, 2);
v___x_1300_ = lean_apply_2(v_k_1297_, v_i_1298_, v_type_1299_);
return v___x_1300_;
}
case 2:
{
lean_object* v_i_1301_; lean_object* v___x_1302_; 
v_i_1301_ = lean_ctor_get(v_t_1296_, 0);
lean_inc(v_i_1301_);
lean_dec_ref_known(v_t_1296_, 1);
v___x_1302_ = lean_apply_1(v_k_1297_, v_i_1301_);
return v___x_1302_;
}
case 3:
{
lean_object* v_sz_1303_; lean_object* v_offset_1304_; lean_object* v_type_1305_; lean_object* v___x_1306_; 
v_sz_1303_ = lean_ctor_get(v_t_1296_, 0);
lean_inc(v_sz_1303_);
v_offset_1304_ = lean_ctor_get(v_t_1296_, 1);
lean_inc(v_offset_1304_);
v_type_1305_ = lean_ctor_get(v_t_1296_, 2);
lean_inc_ref(v_type_1305_);
lean_dec_ref_known(v_t_1296_, 3);
v___x_1306_ = lean_apply_3(v_k_1297_, v_sz_1303_, v_offset_1304_, v_type_1305_);
return v___x_1306_;
}
case 5:
{
lean_object* v_depth_1307_; lean_object* v_i_1308_; lean_object* v_type_1309_; lean_object* v___x_1310_; 
v_depth_1307_ = lean_ctor_get(v_t_1296_, 0);
lean_inc(v_depth_1307_);
v_i_1308_ = lean_ctor_get(v_t_1296_, 1);
lean_inc(v_i_1308_);
v_type_1309_ = lean_ctor_get(v_t_1296_, 2);
lean_inc_ref(v_type_1309_);
lean_dec_ref_known(v_t_1296_, 3);
v___x_1310_ = lean_apply_3(v_k_1297_, v_depth_1307_, v_i_1308_, v_type_1309_);
return v___x_1310_;
}
default: 
{
lean_dec(v_t_1296_);
return v_k_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim(lean_object* v_motive_1311_, lean_object* v_ctorIdx_1312_, lean_object* v_t_1313_, lean_object* v_h_1314_, lean_object* v_k_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1313_, v_k_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___boxed(lean_object* v_motive_1317_, lean_object* v_ctorIdx_1318_, lean_object* v_t_1319_, lean_object* v_h_1320_, lean_object* v_k_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim(v_motive_1317_, v_ctorIdx_1318_, v_t_1319_, v_h_1320_, v_k_1321_);
lean_dec(v_ctorIdx_1318_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_erased_elim___redArg(lean_object* v_t_1323_, lean_object* v_erased_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1323_, v_erased_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_erased_elim(lean_object* v_motive_1326_, lean_object* v_t_1327_, lean_object* v_h_1328_, lean_object* v_erased_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1327_, v_erased_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_object_elim___redArg(lean_object* v_t_1331_, lean_object* v_object_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1331_, v_object_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_object_elim(lean_object* v_motive_1334_, lean_object* v_t_1335_, lean_object* v_h_1336_, lean_object* v_object_1337_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1335_, v_object_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_usize_elim___redArg(lean_object* v_t_1339_, lean_object* v_usize_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1339_, v_usize_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_usize_elim(lean_object* v_motive_1342_, lean_object* v_t_1343_, lean_object* v_h_1344_, lean_object* v_usize_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1343_, v_usize_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_scalar_elim___redArg(lean_object* v_t_1347_, lean_object* v_scalar_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1347_, v_scalar_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_scalar_elim(lean_object* v_motive_1350_, lean_object* v_t_1351_, lean_object* v_h_1352_, lean_object* v_scalar_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1351_, v_scalar_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_void_elim___redArg(lean_object* v_t_1355_, lean_object* v_void_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1355_, v_void_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_void_elim(lean_object* v_motive_1358_, lean_object* v_t_1359_, lean_object* v_h_1360_, lean_object* v_void_1361_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1359_, v_void_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_spilled_elim___redArg(lean_object* v_t_1363_, lean_object* v_spilled_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1363_, v_spilled_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_spilled_elim(lean_object* v_motive_1366_, lean_object* v_t_1367_, lean_object* v_h_1368_, lean_object* v_spilled_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1367_, v_spilled_1369_);
return v___x_1370_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo_default(void){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_box(0);
return v___x_1371_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo(void){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_box(0);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format(lean_object* v_x_1397_){
_start:
{
switch(lean_obj_tag(v_x_1397_))
{
case 0:
{
lean_object* v___x_1398_; 
v___x_1398_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__1));
return v___x_1398_;
}
case 1:
{
lean_object* v_i_1399_; lean_object* v_type_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1415_; 
v_i_1399_ = lean_ctor_get(v_x_1397_, 0);
v_type_1400_ = lean_ctor_get(v_x_1397_, 1);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_x_1397_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1402_ = v_x_1397_;
v_isShared_1403_ = v_isSharedCheck_1415_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_type_1400_);
lean_inc(v_i_1399_);
lean_dec(v_x_1397_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1415_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1404_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__3));
v___x_1405_ = l_Nat_reprFast(v_i_1399_);
v___x_1406_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 5);
lean_ctor_set(v___x_1402_, 1, v___x_1406_);
lean_ctor_set(v___x_1402_, 0, v___x_1404_);
v___x_1408_ = v___x_1402_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1409_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5));
v___x_1410_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = lean_expr_dbg_to_string(v_type_1400_);
lean_dec_ref(v_type_1400_);
v___x_1412_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1410_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
return v___x_1413_;
}
}
}
case 2:
{
lean_object* v_i_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1426_; 
v_i_1416_ = lean_ctor_get(v_x_1397_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_x_1397_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1418_ = v_x_1397_;
v_isShared_1419_ = v_isSharedCheck_1426_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_i_1416_);
lean_dec(v_x_1397_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1426_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1420_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__7));
v___x_1421_ = l_Nat_reprFast(v_i_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set_tag(v___x_1418_, 3);
lean_ctor_set(v___x_1418_, 0, v___x_1421_);
v___x_1423_ = v___x_1418_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1420_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
return v___x_1424_;
}
}
}
case 3:
{
lean_object* v_sz_1427_; lean_object* v_offset_1428_; lean_object* v_type_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v_sz_1427_ = lean_ctor_get(v_x_1397_, 0);
lean_inc(v_sz_1427_);
v_offset_1428_ = lean_ctor_get(v_x_1397_, 1);
lean_inc(v_offset_1428_);
v_type_1429_ = lean_ctor_get(v_x_1397_, 2);
lean_inc_ref(v_type_1429_);
lean_dec_ref_known(v_x_1397_, 3);
v___x_1430_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__9));
v___x_1431_ = l_Nat_reprFast(v_sz_1427_);
v___x_1432_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
v___x_1433_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1430_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__11));
v___x_1435_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = l_Nat_reprFast(v_offset_1428_);
v___x_1437_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
v___x_1438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1435_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5));
v___x_1440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1438_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = lean_expr_dbg_to_string(v_type_1429_);
lean_dec_ref(v_type_1429_);
v___x_1442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
v___x_1443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1440_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
return v___x_1443_;
}
case 4:
{
lean_object* v___x_1444_; 
v___x_1444_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__13));
return v___x_1444_;
}
default: 
{
lean_object* v_depth_1445_; lean_object* v_i_1446_; lean_object* v_type_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_depth_1445_ = lean_ctor_get(v_x_1397_, 0);
lean_inc(v_depth_1445_);
v_i_1446_ = lean_ctor_get(v_x_1397_, 1);
lean_inc(v_i_1446_);
v_type_1447_ = lean_ctor_get(v_x_1397_, 2);
lean_inc_ref(v_type_1447_);
lean_dec_ref_known(v_x_1397_, 3);
v___x_1448_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__3));
v___x_1449_ = l_Nat_reprFast(v_depth_1445_);
v___x_1450_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
v___x_1451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1448_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__15));
v___x_1453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1451_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = l_Nat_reprFast(v_i_1446_);
v___x_1455_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
v___x_1456_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1453_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5));
v___x_1458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = lean_expr_dbg_to_string(v_type_1447_);
lean_dec_ref(v_type_1447_);
v___x_1460_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
v___x_1461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1458_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
return v___x_1461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_spillDepth(lean_object* v_x_1462_){
_start:
{
if (lean_obj_tag(v_x_1462_) == 5)
{
lean_object* v_depth_1463_; 
v_depth_1463_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_depth_1463_);
return v_depth_1463_;
}
else
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_unsigned_to_nat(0u);
return v___x_1464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_spillDepth___boxed(lean_object* v_x_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Compiler_LCNF_CtorFieldInfo_spillDepth(v_x_1465_);
lean_dec(v_x_1465_);
return v_res_1466_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_spillLinkIdx___closed__0(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = lean_unsigned_to_nat(1u);
v___x_1470_ = l_Lean_maxCtorNumObjs;
v___x_1471_ = lean_nat_sub(v___x_1470_, v___x_1469_);
return v___x_1471_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_spillLinkIdx(void){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_obj_once(&l_Lean_Compiler_LCNF_spillLinkIdx___closed__0, &l_Lean_Compiler_LCNF_spillLinkIdx___closed__0_once, _init_l_Lean_Compiler_LCNF_spillLinkIdx___closed__0);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_numSpillObjs(lean_object* v_numObjs_1473_){
_start:
{
lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1474_ = l_Lean_maxCtorNumObjs;
v___x_1475_ = lean_nat_dec_le(v_numObjs_1473_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1476_ = lean_unsigned_to_nat(1u);
v___x_1477_ = lean_nat_sub(v_numObjs_1473_, v___x_1476_);
v___x_1478_ = l_Lean_Compiler_LCNF_spillLinkIdx;
v___x_1479_ = lean_nat_div(v___x_1477_, v___x_1478_);
lean_dec(v___x_1477_);
return v___x_1479_;
}
else
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_unsigned_to_nat(0u);
return v___x_1480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_numSpillObjs___boxed(lean_object* v_numObjs_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_Compiler_LCNF_numSpillObjs(v_numObjs_1481_);
lean_dec(v_numObjs_1481_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_spillCtorInfo(lean_object* v_ctorName_1486_, lean_object* v_size_1487_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1488_ = ((lean_object*)(l_Lean_Compiler_LCNF_spillCtorInfo___closed__1));
v___x_1489_ = l_Lean_Name_append(v_ctorName_1486_, v___x_1488_);
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
lean_ctor_set(v___x_1491_, 2, v_size_1487_);
lean_ctor_set(v___x_1491_, 3, v___x_1490_);
lean_ctor_set(v___x_1491_, 4, v___x_1490_);
return v___x_1491_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1494_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0));
v___x_1495_ = l_Lean_Compiler_LCNF_instInhabitedCtorInfo_default;
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
lean_ctor_set(v___x_1496_, 1, v___x_1494_);
return v___x_1496_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default(void){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1);
return v___x_1497_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout(void){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_init_1499_, lean_object* v_x_1500_){
_start:
{
if (lean_obj_tag(v_x_1500_) == 0)
{
lean_object* v_k_1501_; lean_object* v_v_1502_; lean_object* v_l_1503_; lean_object* v_r_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v_k_1501_ = lean_ctor_get(v_x_1500_, 1);
v_v_1502_ = lean_ctor_get(v_x_1500_, 2);
v_l_1503_ = lean_ctor_get(v_x_1500_, 3);
v_r_1504_ = lean_ctor_get(v_x_1500_, 4);
v___x_1505_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(v_init_1499_, v_l_1503_);
lean_inc(v_v_1502_);
lean_inc(v_k_1501_);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v_k_1501_);
lean_ctor_set(v___x_1506_, 1, v_v_1502_);
v___x_1507_ = lean_array_push(v___x_1505_, v___x_1506_);
v_init_1499_ = v___x_1507_;
v_x_1500_ = v_r_1504_;
goto _start;
}
else
{
return v_init_1499_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_init_1509_, lean_object* v_x_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(v_init_1509_, v_x_1510_);
lean_dec(v_x_1510_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2(lean_object* v_env_1512_, lean_object* v_as_1513_, size_t v_i_1514_, size_t v_stop_1515_, lean_object* v_b_1516_){
_start:
{
lean_object* v___y_1518_; uint8_t v___x_1522_; 
v___x_1522_ = lean_usize_dec_eq(v_i_1514_, v_stop_1515_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v_fst_1524_; uint8_t v___x_1525_; 
v___x_1523_ = lean_array_uget_borrowed(v_as_1513_, v_i_1514_);
v_fst_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_fst_1524_);
lean_inc_ref(v_env_1512_);
v___x_1525_ = l_Lean_Environment_contains(v_env_1512_, v_fst_1524_, v___x_1522_);
if (v___x_1525_ == 0)
{
v___y_1518_ = v_b_1516_;
goto v___jp_1517_;
}
else
{
lean_object* v___x_1526_; 
lean_inc(v___x_1523_);
v___x_1526_ = lean_array_push(v_b_1516_, v___x_1523_);
v___y_1518_ = v___x_1526_;
goto v___jp_1517_;
}
}
else
{
lean_dec_ref(v_env_1512_);
return v_b_1516_;
}
v___jp_1517_:
{
size_t v___x_1519_; size_t v___x_1520_; 
v___x_1519_ = ((size_t)1ULL);
v___x_1520_ = lean_usize_add(v_i_1514_, v___x_1519_);
v_i_1514_ = v___x_1520_;
v_b_1516_ = v___y_1518_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_1527_, lean_object* v_as_1528_, lean_object* v_i_1529_, lean_object* v_stop_1530_, lean_object* v_b_1531_){
_start:
{
size_t v_i_boxed_1532_; size_t v_stop_boxed_1533_; lean_object* v_res_1534_; 
v_i_boxed_1532_ = lean_unbox_usize(v_i_1529_);
lean_dec(v_i_1529_);
v_stop_boxed_1533_ = lean_unbox_usize(v_stop_1530_);
lean_dec(v_stop_1530_);
v_res_1534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2(v_env_1527_, v_as_1528_, v_i_boxed_1532_, v_stop_boxed_1533_, v_b_1531_);
lean_dec_ref(v_as_1528_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(lean_object* v_env_1535_, lean_object* v_as_1536_, size_t v_i_1537_, size_t v_stop_1538_, lean_object* v_b_1539_){
_start:
{
lean_object* v___y_1541_; uint8_t v___x_1545_; 
v___x_1545_ = lean_usize_dec_eq(v_i_1537_, v_stop_1538_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v_fst_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1546_ = lean_array_uget_borrowed(v_as_1536_, v_i_1537_);
v_fst_1547_ = lean_ctor_get(v___x_1546_, 0);
v___x_1548_ = 1;
lean_inc_ref(v_env_1535_);
v___x_1549_ = l_Lean_Environment_setExporting(v_env_1535_, v___x_1548_);
lean_inc(v_fst_1547_);
v___x_1550_ = l_Lean_Environment_contains(v___x_1549_, v_fst_1547_, v___x_1548_);
if (v___x_1550_ == 0)
{
v___y_1541_ = v_b_1539_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1551_; 
lean_inc(v___x_1546_);
v___x_1551_ = lean_array_push(v_b_1539_, v___x_1546_);
v___y_1541_ = v___x_1551_;
goto v___jp_1540_;
}
}
else
{
lean_dec_ref(v_env_1535_);
return v_b_1539_;
}
v___jp_1540_:
{
size_t v___x_1542_; size_t v___x_1543_; 
v___x_1542_ = ((size_t)1ULL);
v___x_1543_ = lean_usize_add(v_i_1537_, v___x_1542_);
v_i_1537_ = v___x_1543_;
v_b_1539_ = v___y_1541_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_1552_, lean_object* v_as_1553_, lean_object* v_i_1554_, lean_object* v_stop_1555_, lean_object* v_b_1556_){
_start:
{
size_t v_i_boxed_1557_; size_t v_stop_boxed_1558_; lean_object* v_res_1559_; 
v_i_boxed_1557_ = lean_unbox_usize(v_i_1554_);
lean_dec(v_i_1554_);
v_stop_boxed_1558_ = lean_unbox_usize(v_stop_1555_);
lean_dec(v_stop_1555_);
v_res_1559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(v_env_1552_, v_as_1553_, v_i_boxed_1557_, v_stop_boxed_1558_, v_b_1556_);
lean_dec_ref(v_as_1553_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(lean_object* v___x_1560_, lean_object* v_env_1561_, lean_object* v_s_1562_){
_start:
{
lean_object* v___y_1564_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1579_ = lean_mk_empty_array_with_capacity(v___x_1560_);
v___x_1580_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(v___x_1579_, v_s_1562_);
v___x_1581_ = lean_array_get_size(v___x_1580_);
v___x_1582_ = lean_mk_empty_array_with_capacity(v___x_1560_);
v___x_1583_ = lean_nat_dec_lt(v___x_1560_, v___x_1581_);
if (v___x_1583_ == 0)
{
lean_dec_ref(v___x_1580_);
v___y_1564_ = v___x_1582_;
goto v___jp_1563_;
}
else
{
uint8_t v___x_1584_; 
v___x_1584_ = lean_nat_dec_le(v___x_1581_, v___x_1581_);
if (v___x_1584_ == 0)
{
if (v___x_1583_ == 0)
{
lean_dec_ref(v___x_1580_);
v___y_1564_ = v___x_1582_;
goto v___jp_1563_;
}
else
{
size_t v___x_1585_; size_t v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = ((size_t)0ULL);
v___x_1586_ = lean_usize_of_nat(v___x_1581_);
lean_inc_ref(v_env_1561_);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2(v_env_1561_, v___x_1580_, v___x_1585_, v___x_1586_, v___x_1582_);
lean_dec_ref(v___x_1580_);
v___y_1564_ = v___x_1587_;
goto v___jp_1563_;
}
}
else
{
size_t v___x_1588_; size_t v___x_1589_; lean_object* v___x_1590_; 
v___x_1588_ = ((size_t)0ULL);
v___x_1589_ = lean_usize_of_nat(v___x_1581_);
lean_inc_ref(v_env_1561_);
v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2(v_env_1561_, v___x_1580_, v___x_1588_, v___x_1589_, v___x_1582_);
lean_dec_ref(v___x_1580_);
v___y_1564_ = v___x_1590_;
goto v___jp_1563_;
}
}
v___jp_1563_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1565_ = lean_array_get_size(v___y_1564_);
v___x_1566_ = lean_mk_empty_array_with_capacity(v___x_1560_);
v___x_1567_ = lean_nat_dec_lt(v___x_1560_, v___x_1565_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
lean_dec_ref(v_env_1561_);
lean_inc_ref(v___x_1566_);
v___x_1568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1566_);
lean_ctor_set(v___x_1568_, 2, v___y_1564_);
return v___x_1568_;
}
else
{
uint8_t v___x_1569_; 
v___x_1569_ = lean_nat_dec_le(v___x_1565_, v___x_1565_);
if (v___x_1569_ == 0)
{
if (v___x_1567_ == 0)
{
lean_object* v___x_1570_; 
lean_dec_ref(v_env_1561_);
lean_inc_ref(v___x_1566_);
v___x_1570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1566_);
lean_ctor_set(v___x_1570_, 1, v___x_1566_);
lean_ctor_set(v___x_1570_, 2, v___y_1564_);
return v___x_1570_;
}
else
{
size_t v___x_1571_; size_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1571_ = ((size_t)0ULL);
v___x_1572_ = lean_usize_of_nat(v___x_1565_);
v___x_1573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(v_env_1561_, v___y_1564_, v___x_1571_, v___x_1572_, v___x_1566_);
lean_inc_ref(v___x_1573_);
v___x_1574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
lean_ctor_set(v___x_1574_, 2, v___y_1564_);
return v___x_1574_;
}
}
else
{
size_t v___x_1575_; size_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1575_ = ((size_t)0ULL);
v___x_1576_ = lean_usize_of_nat(v___x_1565_);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(v_env_1561_, v___y_1564_, v___x_1575_, v___x_1576_, v___x_1566_);
lean_inc_ref(v___x_1577_);
v___x_1578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
lean_ctor_set(v___x_1578_, 2, v___y_1564_);
return v___x_1578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2____boxed(lean_object* v___x_1591_, lean_object* v_env_1592_, lean_object* v_s_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(v___x_1591_, v_env_1592_, v_s_1593_);
lean_dec(v_s_1593_);
lean_dec(v___x_1591_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; lean_object* v___x_1606_; 
v___f_1602_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_));
v___x_1603_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_));
v___x_1604_ = lean_box(0);
v___x_1605_ = 0;
v___x_1606_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_1603_, v___x_1604_, v___x_1605_, v___f_1602_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2____boxed(lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_();
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(lean_object* v_init_1609_, lean_object* v_t_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(v_init_1609_, v_t_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1___boxed(lean_object* v_init_1612_, lean_object* v_t_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(v_init_1612_, v_t_1613_);
lean_dec(v_t_1613_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout(lean_object* v_layout_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_ctorInfo_1619_; lean_object* v___x_1620_; 
v_ctorInfo_1619_ = lean_ctor_get(v_layout_1615_, 0);
lean_inc_ref(v_ctorInfo_1619_);
lean_dec_ref(v_layout_1615_);
v___x_1620_ = l_Lean_Compiler_LCNF_CtorInfo_checkValid(v_ctorInfo_1619_, v_a_1616_, v_a_1617_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout___boxed(lean_object* v_layout_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout(v_layout_1621_, v_a_1622_, v_a_1623_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(lean_object* v_msg_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___f_1630_; lean_object* v___x_11980__overap_1631_; lean_object* v___x_1632_; 
v___f_1630_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0));
v___x_11980__overap_1631_ = lean_panic_fn_borrowed(v___f_1630_, v_msg_1626_);
lean_inc(v___y_1628_);
lean_inc_ref(v___y_1627_);
v___x_1632_ = lean_apply_3(v___x_11980__overap_1631_, v___y_1627_, v___y_1628_, lean_box(0));
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1___boxed(lean_object* v_msg_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(v_msg_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(lean_object* v_msg_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___f_1645_; lean_object* v___x_11990__overap_1646_; lean_object* v___x_1647_; 
v___f_1645_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___closed__0));
v___x_11990__overap_1646_ = lean_panic_fn_borrowed(v___f_1645_, v_msg_1639_);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
lean_inc(v___y_1641_);
lean_inc_ref(v___y_1640_);
v___x_1647_ = lean_apply_5(v___x_11990__overap_1646_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, lean_box(0));
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___boxed(lean_object* v_msg_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(v_msg_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___redArg(lean_object* v_type_1655_, lean_object* v_k_1656_, uint8_t v_cleanupAnnotations_1657_, uint8_t v_whnfType_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___f_1664_; lean_object* v___x_1665_; 
v___f_1664_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1664_, 0, v_k_1656_);
v___x_1665_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1655_, v___f_1664_, v_cleanupAnnotations_1657_, v_whnfType_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
v_a_1674_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1665_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1665_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___redArg___boxed(lean_object* v_type_1682_, lean_object* v_k_1683_, lean_object* v_cleanupAnnotations_1684_, lean_object* v_whnfType_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1691_; uint8_t v_whnfType_boxed_1692_; lean_object* v_res_1693_; 
v_cleanupAnnotations_boxed_1691_ = lean_unbox(v_cleanupAnnotations_1684_);
v_whnfType_boxed_1692_ = lean_unbox(v_whnfType_1685_);
v_res_1693_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___redArg(v_type_1682_, v_k_1683_, v_cleanupAnnotations_boxed_1691_, v_whnfType_boxed_1692_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6(lean_object* v_00_u03b1_1694_, lean_object* v_type_1695_, lean_object* v_k_1696_, uint8_t v_cleanupAnnotations_1697_, uint8_t v_whnfType_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___redArg(v_type_1695_, v_k_1696_, v_cleanupAnnotations_1697_, v_whnfType_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___boxed(lean_object* v_00_u03b1_1705_, lean_object* v_type_1706_, lean_object* v_k_1707_, lean_object* v_cleanupAnnotations_1708_, lean_object* v_whnfType_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1715_; uint8_t v_whnfType_boxed_1716_; lean_object* v_res_1717_; 
v_cleanupAnnotations_boxed_1715_ = lean_unbox(v_cleanupAnnotations_1708_);
v_whnfType_boxed_1716_ = lean_unbox(v_whnfType_1709_);
v_res_1717_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6(v_00_u03b1_1705_, v_type_1706_, v_k_1707_, v_cleanupAnnotations_boxed_1715_, v_whnfType_boxed_1716_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(lean_object* v_size_1718_, size_t v_sz_1719_, size_t v_i_1720_, lean_object* v_bs_1721_, lean_object* v___y_1722_){
_start:
{
uint8_t v___x_1723_; 
v___x_1723_ = lean_usize_dec_lt(v_i_1720_, v_sz_1719_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v_bs_1721_);
lean_ctor_set(v___x_1724_, 1, v___y_1722_);
return v___x_1724_;
}
else
{
lean_object* v_v_1725_; lean_object* v___x_1726_; lean_object* v_bs_x27_1727_; lean_object* v_fst_1729_; lean_object* v_snd_1730_; 
v_v_1725_ = lean_array_uget(v_bs_1721_, v_i_1720_);
v___x_1726_ = lean_unsigned_to_nat(0u);
v_bs_x27_1727_ = lean_array_uset(v_bs_1721_, v_i_1720_, v___x_1726_);
if (lean_obj_tag(v_v_1725_) == 3)
{
lean_object* v_sz_1735_; lean_object* v_type_1736_; uint8_t v___x_1737_; 
v_sz_1735_ = lean_ctor_get(v_v_1725_, 0);
v_type_1736_ = lean_ctor_get(v_v_1725_, 2);
v___x_1737_ = lean_nat_dec_eq(v_sz_1735_, v_size_1718_);
if (v___x_1737_ == 0)
{
v_fst_1729_ = v_v_1725_;
v_snd_1730_ = v___y_1722_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1745_; 
lean_inc_ref(v_type_1736_);
lean_inc(v_sz_1735_);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_v_1725_);
if (v_isSharedCheck_1745_ == 0)
{
lean_object* v_unused_1746_; lean_object* v_unused_1747_; lean_object* v_unused_1748_; 
v_unused_1746_ = lean_ctor_get(v_v_1725_, 2);
lean_dec(v_unused_1746_);
v_unused_1747_ = lean_ctor_get(v_v_1725_, 1);
lean_dec(v_unused_1747_);
v_unused_1748_ = lean_ctor_get(v_v_1725_, 0);
lean_dec(v_unused_1748_);
v___x_1739_ = v_v_1725_;
v_isShared_1740_ = v_isSharedCheck_1745_;
goto v_resetjp_1738_;
}
else
{
lean_dec(v_v_1725_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1745_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1743_; 
v___x_1741_ = lean_nat_add(v___y_1722_, v_sz_1735_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 1, v___y_1722_);
v___x_1743_ = v___x_1739_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_sz_1735_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___y_1722_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v_type_1736_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
v_fst_1729_ = v___x_1743_;
v_snd_1730_ = v___x_1741_;
goto v___jp_1728_;
}
}
}
}
else
{
v_fst_1729_ = v_v_1725_;
v_snd_1730_ = v___y_1722_;
goto v___jp_1728_;
}
v___jp_1728_:
{
size_t v___x_1731_; size_t v___x_1732_; lean_object* v___x_1733_; 
v___x_1731_ = ((size_t)1ULL);
v___x_1732_ = lean_usize_add(v_i_1720_, v___x_1731_);
v___x_1733_ = lean_array_uset(v_bs_x27_1727_, v_i_1720_, v_fst_1729_);
v_i_1720_ = v___x_1732_;
v_bs_1721_ = v___x_1733_;
v___y_1722_ = v_snd_1730_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0___boxed(lean_object* v_size_1749_, lean_object* v_sz_1750_, lean_object* v_i_1751_, lean_object* v_bs_1752_, lean_object* v___y_1753_){
_start:
{
size_t v_sz_boxed_1754_; size_t v_i_boxed_1755_; lean_object* v_res_1756_; 
v_sz_boxed_1754_ = lean_unbox_usize(v_sz_1750_);
lean_dec(v_sz_1750_);
v_i_boxed_1755_ = lean_unbox_usize(v_i_1751_);
lean_dec(v_i_1751_);
v_res_1756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(v_size_1749_, v_sz_boxed_1754_, v_i_boxed_1755_, v_bs_1752_, v___y_1753_);
lean_dec(v_size_1749_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0(lean_object* v_fields_1757_, lean_object* v_size_1758_, lean_object* v_nextOffset_1759_){
_start:
{
size_t v_sz_1760_; size_t v___x_1761_; lean_object* v___x_1762_; 
v_sz_1760_ = lean_array_size(v_fields_1757_);
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(v_size_1758_, v_sz_1760_, v___x_1761_, v_fields_1757_, v_nextOffset_1759_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0___boxed(lean_object* v_fields_1763_, lean_object* v_size_1764_, lean_object* v_nextOffset_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0(v_fields_1763_, v_size_1764_, v_nextOffset_1765_);
lean_dec(v_size_1764_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5(size_t v_sz_1767_, size_t v_i_1768_, lean_object* v_bs_1769_){
_start:
{
uint8_t v___x_1770_; 
v___x_1770_ = lean_usize_dec_lt(v_i_1768_, v_sz_1767_);
if (v___x_1770_ == 0)
{
return v_bs_1769_;
}
else
{
lean_object* v_v_1771_; lean_object* v___x_1772_; lean_object* v_bs_x27_1773_; lean_object* v___y_1775_; 
v_v_1771_ = lean_array_uget(v_bs_1769_, v_i_1768_);
v___x_1772_ = lean_unsigned_to_nat(0u);
v_bs_x27_1773_ = lean_array_uset(v_bs_1769_, v_i_1768_, v___x_1772_);
if (lean_obj_tag(v_v_1771_) == 1)
{
lean_object* v_i_1780_; lean_object* v_type_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v_i_1780_ = lean_ctor_get(v_v_1771_, 0);
v_type_1781_ = lean_ctor_get(v_v_1771_, 1);
v___x_1782_ = l_Lean_Compiler_LCNF_spillLinkIdx;
v___x_1783_ = lean_nat_div(v_i_1780_, v___x_1782_);
v___x_1784_ = lean_nat_dec_eq(v___x_1783_, v___x_1772_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_inc_ref(v_type_1781_);
lean_inc(v_i_1780_);
lean_dec_ref_known(v_v_1771_, 2);
v___x_1785_ = lean_nat_mod(v_i_1780_, v___x_1782_);
lean_dec(v_i_1780_);
v___x_1786_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1783_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
lean_ctor_set(v___x_1786_, 2, v_type_1781_);
v___y_1775_ = v___x_1786_;
goto v___jp_1774_;
}
else
{
lean_dec(v___x_1783_);
v___y_1775_ = v_v_1771_;
goto v___jp_1774_;
}
}
else
{
v___y_1775_ = v_v_1771_;
goto v___jp_1774_;
}
v___jp_1774_:
{
size_t v___x_1776_; size_t v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = ((size_t)1ULL);
v___x_1777_ = lean_usize_add(v_i_1768_, v___x_1776_);
v___x_1778_ = lean_array_uset(v_bs_x27_1773_, v_i_1768_, v___y_1775_);
v_i_1768_ = v___x_1777_;
v_bs_1769_ = v___x_1778_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___boxed(lean_object* v_sz_1787_, lean_object* v_i_1788_, lean_object* v_bs_1789_){
_start:
{
size_t v_sz_boxed_1790_; size_t v_i_boxed_1791_; lean_object* v_res_1792_; 
v_sz_boxed_1790_ = lean_unbox_usize(v_sz_1787_);
lean_dec(v_sz_1787_);
v_i_boxed_1791_ = lean_unbox_usize(v_i_1788_);
lean_dec(v_i_1788_);
v_res_1792_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5(v_sz_boxed_1790_, v_i_boxed_1791_, v_bs_1789_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(size_t v_sz_1793_, size_t v_i_1794_, lean_object* v_bs_1795_, lean_object* v___y_1796_){
_start:
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_usize_dec_lt(v_i_1794_, v_sz_1793_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_bs_1795_);
lean_ctor_set(v___x_1798_, 1, v___y_1796_);
return v___x_1798_;
}
else
{
lean_object* v_v_1799_; lean_object* v___x_1800_; lean_object* v_bs_x27_1801_; lean_object* v_fst_1803_; lean_object* v_snd_1804_; 
v_v_1799_ = lean_array_uget(v_bs_1795_, v_i_1794_);
v___x_1800_ = lean_unsigned_to_nat(0u);
v_bs_x27_1801_ = lean_array_uset(v_bs_1795_, v_i_1794_, v___x_1800_);
if (lean_obj_tag(v_v_1799_) == 2)
{
lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1817_; 
v_isSharedCheck_1817_ = !lean_is_exclusive(v_v_1799_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; 
v_unused_1818_ = lean_ctor_get(v_v_1799_, 0);
lean_dec(v_unused_1818_);
v___x_1810_ = v_v_1799_;
v_isShared_1811_ = v_isSharedCheck_1817_;
goto v_resetjp_1809_;
}
else
{
lean_dec(v_v_1799_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1817_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1812_ = lean_unsigned_to_nat(1u);
v___x_1813_ = lean_nat_add(v___y_1796_, v___x_1812_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___y_1796_);
v___x_1815_ = v___x_1810_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___y_1796_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
v_fst_1803_ = v___x_1815_;
v_snd_1804_ = v___x_1813_;
goto v___jp_1802_;
}
}
}
else
{
v_fst_1803_ = v_v_1799_;
v_snd_1804_ = v___y_1796_;
goto v___jp_1802_;
}
v___jp_1802_:
{
size_t v___x_1805_; size_t v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = ((size_t)1ULL);
v___x_1806_ = lean_usize_add(v_i_1794_, v___x_1805_);
v___x_1807_ = lean_array_uset(v_bs_x27_1801_, v_i_1794_, v_fst_1803_);
v_i_1794_ = v___x_1806_;
v_bs_1795_ = v___x_1807_;
v___y_1796_ = v_snd_1804_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4___boxed(lean_object* v_sz_1819_, lean_object* v_i_1820_, lean_object* v_bs_1821_, lean_object* v___y_1822_){
_start:
{
size_t v_sz_boxed_1823_; size_t v_i_boxed_1824_; lean_object* v_res_1825_; 
v_sz_boxed_1823_ = lean_unbox_usize(v_sz_1819_);
lean_dec(v_sz_1819_);
v_i_boxed_1824_ = lean_unbox_usize(v_i_1820_);
lean_dec(v_i_1820_);
v_res_1825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(v_sz_boxed_1823_, v_i_boxed_1824_, v_bs_1821_, v___y_1822_);
return v_res_1825_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1827_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_1828_ = lean_unsigned_to_nat(15u);
v___x_1829_ = lean_unsigned_to_nat(266u);
v___x_1830_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0));
v___x_1831_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_1832_ = l_mkPanicMessageWithDecl(v___x_1831_, v___x_1830_, v___x_1829_, v___x_1828_, v___x_1827_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(lean_object* v___f_1833_, lean_object* v_fst_1834_, lean_object* v_fst_1835_, lean_object* v_fst_1836_, lean_object* v_fst_1837_, lean_object* v_snd_1838_, lean_object* v_x_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1);
v___x_1846_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(v___x_1845_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1848_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1846_, 1);
lean_inc(v___y_1843_);
lean_inc_ref(v___y_1842_);
lean_inc(v___y_1841_);
lean_inc_ref(v___y_1840_);
v___x_1848_ = lean_apply_11(v___f_1833_, v_a_1847_, v_fst_1834_, v_fst_1835_, v_fst_1836_, v_fst_1837_, v_snd_1838_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, lean_box(0));
return v___x_1848_;
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_snd_1838_);
lean_dec(v_fst_1837_);
lean_dec(v_fst_1836_);
lean_dec(v_fst_1835_);
lean_dec(v_fst_1834_);
lean_dec_ref(v___f_1833_);
v_a_1849_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1846_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1846_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___boxed(lean_object* v___f_1857_, lean_object* v_fst_1858_, lean_object* v_fst_1859_, lean_object* v_fst_1860_, lean_object* v_fst_1861_, lean_object* v_snd_1862_, lean_object* v_x_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1857_, v_fst_1858_, v_fst_1859_, v_fst_1860_, v_fst_1861_, v_snd_1862_, v_x_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec_ref(v_x_1863_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(lean_object* v_fst_1870_, lean_object* v_ctorField_1871_, lean_object* v_nextIdx_1872_, uint8_t v_has1BScalar_1873_, uint8_t v_has2BScalar_1874_, uint8_t v_has4BScalar_1875_, uint8_t v_has8BScalar_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1882_ = lean_array_push(v_fst_1870_, v_ctorField_1871_);
v___x_1883_ = lean_box(v_has4BScalar_1875_);
v___x_1884_ = lean_box(v_has8BScalar_1876_);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1883_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = lean_box(v_has2BScalar_1874_);
v___x_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
lean_ctor_set(v___x_1887_, 1, v___x_1885_);
v___x_1888_ = lean_box(v_has1BScalar_1873_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v___x_1887_);
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v_nextIdx_1872_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1882_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0___boxed(lean_object* v_fst_1894_, lean_object* v_ctorField_1895_, lean_object* v_nextIdx_1896_, lean_object* v_has1BScalar_1897_, lean_object* v_has2BScalar_1898_, lean_object* v_has4BScalar_1899_, lean_object* v_has8BScalar_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
uint8_t v_has1BScalar_boxed_1906_; uint8_t v_has2BScalar_boxed_1907_; uint8_t v_has4BScalar_boxed_1908_; uint8_t v_has8BScalar_boxed_1909_; lean_object* v_res_1910_; 
v_has1BScalar_boxed_1906_ = lean_unbox(v_has1BScalar_1897_);
v_has2BScalar_boxed_1907_ = lean_unbox(v_has2BScalar_1898_);
v_has4BScalar_boxed_1908_ = lean_unbox(v_has4BScalar_1899_);
v_has8BScalar_boxed_1909_ = lean_unbox(v_has8BScalar_1900_);
v_res_1910_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1894_, v_ctorField_1895_, v_nextIdx_1896_, v_has1BScalar_boxed_1906_, v_has2BScalar_boxed_1907_, v_has4BScalar_boxed_1908_, v_has8BScalar_boxed_1909_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(lean_object* v_fst_1911_, lean_object* v___x_1912_, lean_object* v_a_1913_, lean_object* v___f_1914_, lean_object* v_fst_1915_, lean_object* v_fst_1916_, lean_object* v_fst_1917_, lean_object* v_snd_1918_, lean_object* v_00___1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = lean_nat_add(v_fst_1911_, v___x_1912_);
v___x_1926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1926_, 0, v_fst_1911_);
lean_ctor_set(v___x_1926_, 1, v_a_1913_);
lean_inc(v___y_1923_);
lean_inc_ref(v___y_1922_);
lean_inc(v___y_1921_);
lean_inc_ref(v___y_1920_);
v___x_1927_ = lean_apply_11(v___f_1914_, v___x_1926_, v___x_1925_, v_fst_1915_, v_fst_1916_, v_fst_1917_, v_snd_1918_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, lean_box(0));
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2___boxed(lean_object* v_fst_1928_, lean_object* v___x_1929_, lean_object* v_a_1930_, lean_object* v___f_1931_, lean_object* v_fst_1932_, lean_object* v_fst_1933_, lean_object* v_fst_1934_, lean_object* v_snd_1935_, lean_object* v_00___1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1928_, v___x_1929_, v_a_1930_, v___f_1931_, v_fst_1932_, v_fst_1933_, v_fst_1934_, v_snd_1935_, v_00___1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___x_1929_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(lean_object* v_a_1945_, lean_object* v_b_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_array_1952_; lean_object* v_start_1953_; lean_object* v_stop_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_2179_; 
v_array_1952_ = lean_ctor_get(v_a_1945_, 0);
v_start_1953_ = lean_ctor_get(v_a_1945_, 1);
v_stop_1954_ = lean_ctor_get(v_a_1945_, 2);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_a_1945_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_1956_ = v_a_1945_;
v_isShared_1957_ = v_isSharedCheck_2179_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_stop_1954_);
lean_inc(v_start_1953_);
lean_inc(v_array_1952_);
lean_dec(v_a_1945_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_2179_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_nat_dec_lt(v_start_1953_, v_stop_1954_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; 
lean_del_object(v___x_1956_);
lean_dec(v_stop_1954_);
lean_dec(v_start_1953_);
lean_dec_ref(v_array_1952_);
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v_b_1946_);
return v___x_1959_;
}
else
{
lean_object* v_snd_1960_; lean_object* v_snd_1961_; lean_object* v_snd_1962_; lean_object* v_snd_1963_; lean_object* v_fst_1964_; lean_object* v_fst_1965_; lean_object* v_fst_1966_; lean_object* v_fst_1967_; lean_object* v_fst_1968_; lean_object* v_snd_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1974_; 
v_snd_1960_ = lean_ctor_get(v_b_1946_, 1);
lean_inc(v_snd_1960_);
v_snd_1961_ = lean_ctor_get(v_snd_1960_, 1);
lean_inc(v_snd_1961_);
v_snd_1962_ = lean_ctor_get(v_snd_1961_, 1);
lean_inc(v_snd_1962_);
v_snd_1963_ = lean_ctor_get(v_snd_1962_, 1);
lean_inc(v_snd_1963_);
v_fst_1964_ = lean_ctor_get(v_b_1946_, 0);
lean_inc(v_fst_1964_);
lean_dec_ref(v_b_1946_);
v_fst_1965_ = lean_ctor_get(v_snd_1960_, 0);
lean_inc(v_fst_1965_);
lean_dec(v_snd_1960_);
v_fst_1966_ = lean_ctor_get(v_snd_1961_, 0);
lean_inc(v_fst_1966_);
lean_dec(v_snd_1961_);
v_fst_1967_ = lean_ctor_get(v_snd_1962_, 0);
lean_inc(v_fst_1967_);
lean_dec(v_snd_1962_);
v_fst_1968_ = lean_ctor_get(v_snd_1963_, 0);
lean_inc(v_fst_1968_);
v_snd_1969_ = lean_ctor_get(v_snd_1963_, 1);
lean_inc(v_snd_1969_);
lean_dec(v_snd_1963_);
v___x_1970_ = lean_unsigned_to_nat(0u);
v___x_1971_ = lean_unsigned_to_nat(1u);
v___x_1972_ = lean_nat_add(v_start_1953_, v___x_1971_);
lean_inc_ref(v_array_1952_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v___x_1972_);
v___x_1974_ = v___x_1956_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_array_1952_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_stop_1954_);
v___x_1974_ = v_reuseFailAlloc_2178_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___y_1976_; lean_object* v___x_1996_; lean_object* v___f_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1996_ = lean_array_fget(v_array_1952_, v_start_1953_);
lean_dec(v_start_1953_);
lean_dec_ref(v_array_1952_);
lean_inc(v_fst_1964_);
v___f_1997_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1997_, 0, v_fst_1964_);
v___x_1998_ = l_Lean_Expr_fvarId_x21(v___x_1996_);
lean_dec(v___x_1996_);
v___x_1999_ = l_Lean_FVarId_getType___redArg(v___x_1998_, v___y_1947_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2001_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2001_ = l_Lean_Compiler_LCNF_toLCNFType(v_a_2000_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2003_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
v___x_2003_ = l_Lean_Compiler_LCNF_toMonoType(v_a_2002_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = l_Lean_Compiler_LCNF_toImpureType(v_a_2004_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___x_2005_, 1);
if (lean_obj_tag(v_a_2006_) == 4)
{
lean_object* v_declName_2007_; 
v_declName_2007_ = lean_ctor_get(v_a_2006_, 0);
if (lean_obj_tag(v_declName_2007_) == 1)
{
lean_object* v_pre_2008_; 
v_pre_2008_ = lean_ctor_get(v_declName_2007_, 0);
if (lean_obj_tag(v_pre_2008_) == 0)
{
lean_object* v_us_2009_; lean_object* v_str_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v_us_2009_ = lean_ctor_get(v_a_2006_, 1);
v_str_2010_ = lean_ctor_get(v_declName_2007_, 1);
v___x_2011_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__0));
v___x_2012_ = lean_string_dec_eq(v_str_2010_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__0));
v___x_2014_ = lean_string_dec_eq(v_str_2010_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__10));
v___x_2016_ = lean_string_dec_eq(v_str_2010_, v___x_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__1));
v___x_2018_ = lean_string_dec_eq(v_str_2010_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__4));
v___x_2020_ = lean_string_dec_eq(v_str_2010_, v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__6));
v___x_2022_ = lean_string_dec_eq(v_str_2010_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9));
v___x_2024_ = lean_string_dec_eq(v_str_2010_, v___x_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6));
v___x_2026_ = lean_string_dec_eq(v_str_2010_, v___x_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3));
v___x_2028_ = lean_string_dec_eq(v_str_2010_, v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__0));
v___x_2030_ = lean_string_dec_eq(v_str_2010_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; uint8_t v___x_2032_; 
v___x_2031_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__3));
v___x_2032_ = lean_string_dec_eq(v_str_2010_, v___x_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__2));
v___x_2034_ = lean_string_dec_eq(v_str_2010_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; 
lean_dec(v_fst_1964_);
v___x_2035_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v_a_2006_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref_known(v_a_2006_, 2);
v___y_1976_ = v___x_2035_;
goto v___jp_1975_;
}
else
{
lean_inc(v_us_2009_);
lean_inc(v_pre_2008_);
lean_dec_ref_known(v_a_2006_, 2);
if (lean_obj_tag(v_us_2009_) == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; uint8_t v___x_2041_; uint8_t v___x_2042_; lean_object* v___x_2043_; 
lean_dec_ref(v___f_1997_);
lean_dec(v_snd_1969_);
v___x_2036_ = lean_unsigned_to_nat(8u);
v___x_2037_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__20));
v___x_2038_ = l_Lean_Expr_const___override(v___x_2037_, v_us_2009_);
v___x_2039_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2036_);
lean_ctor_set(v___x_2039_, 1, v___x_1970_);
lean_ctor_set(v___x_2039_, 2, v___x_2038_);
v___x_2040_ = lean_unbox(v_fst_1966_);
lean_dec(v_fst_1966_);
v___x_2041_ = lean_unbox(v_fst_1967_);
lean_dec(v_fst_1967_);
v___x_2042_ = lean_unbox(v_fst_1968_);
lean_dec(v_fst_1968_);
v___x_2043_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1964_, v___x_2039_, v_fst_1965_, v___x_2040_, v___x_2041_, v___x_2042_, v___x_2034_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v___y_1976_ = v___x_2043_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
lean_dec(v_fst_1964_);
v___x_2044_ = l_Lean_Name_str___override(v_pre_2008_, v___x_2033_);
v___x_2045_ = l_Lean_Expr_const___override(v___x_2044_, v_us_2009_);
v___x_2046_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2045_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref(v___x_2045_);
v___y_1976_ = v___x_2046_;
goto v___jp_1975_;
}
}
}
else
{
lean_inc(v_us_2009_);
lean_inc(v_pre_2008_);
lean_dec_ref_known(v_a_2006_, 2);
if (lean_obj_tag(v_us_2009_) == 0)
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; uint8_t v___x_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; 
lean_dec_ref(v___f_1997_);
lean_dec(v_fst_1968_);
v___x_2047_ = lean_unsigned_to_nat(4u);
v___x_2048_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__17));
v___x_2049_ = l_Lean_Expr_const___override(v___x_2048_, v_us_2009_);
v___x_2050_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2047_);
lean_ctor_set(v___x_2050_, 1, v___x_1970_);
lean_ctor_set(v___x_2050_, 2, v___x_2049_);
v___x_2051_ = lean_unbox(v_fst_1966_);
lean_dec(v_fst_1966_);
v___x_2052_ = lean_unbox(v_fst_1967_);
lean_dec(v_fst_1967_);
v___x_2053_ = lean_unbox(v_snd_1969_);
lean_dec(v_snd_1969_);
v___x_2054_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1964_, v___x_2050_, v_fst_1965_, v___x_2051_, v___x_2052_, v___x_2032_, v___x_2053_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v___y_1976_ = v___x_2054_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
lean_dec(v_fst_1964_);
v___x_2055_ = l_Lean_Name_str___override(v_pre_2008_, v___x_2031_);
v___x_2056_ = l_Lean_Expr_const___override(v___x_2055_, v_us_2009_);
v___x_2057_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2056_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref(v___x_2056_);
v___y_1976_ = v___x_2057_;
goto v___jp_1975_;
}
}
}
else
{
lean_inc(v_us_2009_);
lean_inc(v_pre_2008_);
lean_dec_ref_known(v_a_2006_, 2);
if (lean_obj_tag(v_us_2009_) == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; uint8_t v___x_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; 
lean_dec_ref(v___f_1997_);
lean_dec(v_snd_1969_);
v___x_2058_ = lean_unsigned_to_nat(8u);
v___x_2059_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__26));
v___x_2060_ = l_Lean_Expr_const___override(v___x_2059_, v_us_2009_);
v___x_2061_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2058_);
lean_ctor_set(v___x_2061_, 1, v___x_1970_);
lean_ctor_set(v___x_2061_, 2, v___x_2060_);
v___x_2062_ = lean_unbox(v_fst_1966_);
lean_dec(v_fst_1966_);
v___x_2063_ = lean_unbox(v_fst_1967_);
lean_dec(v_fst_1967_);
v___x_2064_ = lean_unbox(v_fst_1968_);
lean_dec(v_fst_1968_);
v___x_2065_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1964_, v___x_2061_, v_fst_1965_, v___x_2062_, v___x_2063_, v___x_2064_, v___x_2030_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v___y_1976_ = v___x_2065_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_dec(v_fst_1964_);
v___x_2066_ = l_Lean_Name_str___override(v_pre_2008_, v___x_2029_);
v___x_2067_ = l_Lean_Expr_const___override(v___x_2066_, v_us_2009_);
v___x_2068_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2067_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref(v___x_2067_);
v___y_1976_ = v___x_2068_;
goto v___jp_1975_;
}
}
}
else
{
lean_inc(v_us_2009_);
lean_inc(v_pre_2008_);
lean_dec_ref_known(v_a_2006_, 2);
if (lean_obj_tag(v_us_2009_) == 0)
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; uint8_t v___x_2074_; uint8_t v___x_2075_; lean_object* v___x_2076_; 
lean_dec_ref(v___f_1997_);
lean_dec(v_fst_1968_);
v___x_2069_ = lean_unsigned_to_nat(4u);
v___x_2070_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__4));
v___x_2071_ = l_Lean_Expr_const___override(v___x_2070_, v_us_2009_);
v___x_2072_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2069_);
lean_ctor_set(v___x_2072_, 1, v___x_1970_);
lean_ctor_set(v___x_2072_, 2, v___x_2071_);
v___x_2073_ = lean_unbox(v_fst_1966_);
lean_dec(v_fst_1966_);
v___x_2074_ = lean_unbox(v_fst_1967_);
lean_dec(v_fst_1967_);
v___x_2075_ = lean_unbox(v_snd_1969_);
lean_dec(v_snd_1969_);
v___x_2076_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1964_, v___x_2072_, v_fst_1965_, v___x_2073_, v___x_2074_, v___x_2028_, v___x_2075_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v___y_1976_ = v___x_2076_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
lean_dec(v_fst_1964_);
v___x_2077_ = l_Lean_Name_str___override(v_pre_2008_, v___x_2027_);
v___x_2078_ = l_Lean_Expr_const___override(v___x_2077_, v_us_2009_);
v___x_2079_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2078_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref(v___x_2078_);
v___y_1976_ = v___x_2079_;
goto v___jp_1975_;
}
}
}
else
{
lean_inc(v_us_2009_);
lean_inc(v_pre_2008_);
lean_dec_ref_known(v_a_2006_, 2);
if (lean_obj_tag(v_us_2009_) == 0)
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; uint8_t v___x_2085_; uint8_t v___x_2086_; lean_object* v___x_2087_; 
lean_dec_ref(v___f_1997_);
lean_dec(v_fst_1967_);
v___x_2080_ = lean_unsigned_to_nat(2u);
v___x_2081_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__7));
v___x_2082_ = l_Lean_Expr_const___override(v___x_2081_, v_us_2009_);
v___x_2083_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2080_);
lean_ctor_set(v___x_2083_, 1, v___x_1970_);
lean_ctor_set(v___x_2083_, 2, v___x_2082_);
v___x_2084_ = lean_unbox(v_fst_1966_);
lean_dec(v_fst_1966_);
v___x_2085_ = lean_unbox(v_fst_1968_);
lean_dec(v_fst_1968_);
v___x_2086_ = lean_unbox(v_snd_1969_);
lean_dec(v_snd_1969_);
v___x_2087_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1964_, v___x_2083_, v_fst_1965_, v___x_2084_, v___x_2026_, v___x_2085_, v___x_2086_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v___y_1976_ = v___x_2087_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_dec(v_fst_1964_);
v___x_2088_ = l_Lean_Name_str___override(v_pre_2008_, v___x_2025_);
v___x_2089_ = l_Lean_Expr_const___override(v___x_2088_, v_us_2009_);
v___x_2090_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2089_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref(v___x_2089_);
v___y_1976_ = v___x_2090_;
goto v___jp_1975_;
}
}
}
else
{
lean_inc(v_us_2009_);
lean_inc(v_pre_2008_);
lean_dec_ref_known(v_a_2006_, 2);
if (lean_obj_tag(v_us_2009_) == 0)
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; uint8_t v___x_2095_; uint8_t v___x_2096_; lean_object* v___x_2097_; 
lean_dec_ref(v___f_1997_);
lean_dec(v_fst_1966_);
v___x_2091_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__10));
v___x_2092_ = l_Lean_Expr_const___override(v___x_2091_, v_us_2009_);
v___x_2093_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2093_, 0, v___x_1971_);
lean_ctor_set(v___x_2093_, 1, v___x_1970_);
lean_ctor_set(v___x_2093_, 2, v___x_2092_);
v___x_2094_ = lean_unbox(v_fst_1967_);
lean_dec(v_fst_1967_);
v___x_2095_ = lean_unbox(v_fst_1968_);
lean_dec(v_fst_1968_);
v___x_2096_ = lean_unbox(v_snd_1969_);
lean_dec(v_snd_1969_);
v___x_2097_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1964_, v___x_2093_, v_fst_1965_, v___x_2024_, v___x_2094_, v___x_2095_, v___x_2096_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v___y_1976_ = v___x_2097_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_dec(v_fst_1964_);
v___x_2098_ = l_Lean_Name_str___override(v_pre_2008_, v___x_2023_);
v___x_2099_ = l_Lean_Expr_const___override(v___x_2098_, v_us_2009_);
v___x_2100_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2099_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref(v___x_2099_);
v___y_1976_ = v___x_2100_;
goto v___jp_1975_;
}
}
}
else
{
lean_inc(v_us_2009_);
lean_inc(v_pre_2008_);
lean_dec_ref_known(v_a_2006_, 2);
if (lean_obj_tag(v_us_2009_) == 0)
{
lean_object* v___x_2101_; uint8_t v___x_2102_; uint8_t v___x_2103_; uint8_t v___x_2104_; uint8_t v___x_2105_; lean_object* v___x_2106_; 
lean_dec_ref(v___f_1997_);
v___x_2101_ = lean_box(4);
v___x_2102_ = lean_unbox(v_fst_1966_);
lean_dec(v_fst_1966_);
v___x_2103_ = lean_unbox(v_fst_1967_);
lean_dec(v_fst_1967_);
v___x_2104_ = lean_unbox(v_fst_1968_);
lean_dec(v_fst_1968_);
v___x_2105_ = lean_unbox(v_snd_1969_);
lean_dec(v_snd_1969_);
v___x_2106_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1964_, v___x_2101_, v_fst_1965_, v___x_2102_, v___x_2103_, v___x_2104_, v___x_2105_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v___y_1976_ = v___x_2106_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_dec(v_fst_1964_);
v___x_2107_ = l_Lean_Name_str___override(v_pre_2008_, v___x_2021_);
v___x_2108_ = l_Lean_Expr_const___override(v___x_2107_, v_us_2009_);
v___x_2109_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2108_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref(v___x_2108_);
v___y_1976_ = v___x_2109_;
goto v___jp_1975_;
}
}
}
else
{
lean_inc(v_us_2009_);
lean_inc(v_pre_2008_);
lean_dec_ref_known(v_a_2006_, 2);
if (lean_obj_tag(v_us_2009_) == 0)
{
lean_object* v___x_2110_; uint8_t v___x_2111_; uint8_t v___x_2112_; uint8_t v___x_2113_; uint8_t v___x_2114_; lean_object* v___x_2115_; 
lean_dec_ref(v___f_1997_);
v___x_2110_ = lean_box(0);
v___x_2111_ = lean_unbox(v_fst_1966_);
lean_dec(v_fst_1966_);
v___x_2112_ = lean_unbox(v_fst_1967_);
lean_dec(v_fst_1967_);
v___x_2113_ = lean_unbox(v_fst_1968_);
lean_dec(v_fst_1968_);
v___x_2114_ = lean_unbox(v_snd_1969_);
lean_dec(v_snd_1969_);
v___x_2115_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1964_, v___x_2110_, v_fst_1965_, v___x_2111_, v___x_2112_, v___x_2113_, v___x_2114_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v___y_1976_ = v___x_2115_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec(v_fst_1964_);
v___x_2116_ = l_Lean_Name_str___override(v_pre_2008_, v___x_2019_);
v___x_2117_ = l_Lean_Expr_const___override(v___x_2116_, v_us_2009_);
v___x_2118_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2117_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref(v___x_2117_);
v___y_1976_ = v___x_2118_;
goto v___jp_1975_;
}
}
}
else
{
lean_inc(v_us_2009_);
lean_inc(v_pre_2008_);
lean_dec_ref_known(v_a_2006_, 2);
if (lean_obj_tag(v_us_2009_) == 0)
{
lean_object* v___x_2119_; uint8_t v___x_2120_; uint8_t v___x_2121_; uint8_t v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; 
lean_dec_ref(v___f_1997_);
v___x_2119_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___closed__0));
v___x_2120_ = lean_unbox(v_fst_1966_);
lean_dec(v_fst_1966_);
v___x_2121_ = lean_unbox(v_fst_1967_);
lean_dec(v_fst_1967_);
v___x_2122_ = lean_unbox(v_fst_1968_);
lean_dec(v_fst_1968_);
v___x_2123_ = lean_unbox(v_snd_1969_);
lean_dec(v_snd_1969_);
v___x_2124_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1964_, v___x_2119_, v_fst_1965_, v___x_2120_, v___x_2121_, v___x_2122_, v___x_2123_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v___y_1976_ = v___x_2124_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
lean_dec(v_fst_1964_);
v___x_2125_ = l_Lean_Name_str___override(v_pre_2008_, v___x_2017_);
v___x_2126_ = l_Lean_Expr_const___override(v___x_2125_, v_us_2009_);
v___x_2127_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2126_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref(v___x_2126_);
v___y_1976_ = v___x_2127_;
goto v___jp_1975_;
}
}
}
else
{
lean_dec(v_fst_1964_);
if (lean_obj_tag(v_us_2009_) == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = lean_box(0);
v___x_2129_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1965_, v___x_1971_, v_a_2006_, v___f_1997_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2128_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v___y_1976_ = v___x_2129_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_inc(v_us_2009_);
lean_inc(v_pre_2008_);
lean_dec_ref_known(v_a_2006_, 2);
v___x_2130_ = l_Lean_Name_str___override(v_pre_2008_, v___x_2015_);
v___x_2131_ = l_Lean_Expr_const___override(v___x_2130_, v_us_2009_);
v___x_2132_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2131_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref(v___x_2131_);
v___y_1976_ = v___x_2132_;
goto v___jp_1975_;
}
}
}
else
{
lean_dec(v_fst_1964_);
if (lean_obj_tag(v_us_2009_) == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = lean_box(0);
v___x_2134_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1965_, v___x_1971_, v_a_2006_, v___f_1997_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2133_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v___y_1976_ = v___x_2134_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
lean_inc(v_us_2009_);
lean_inc(v_pre_2008_);
lean_dec_ref_known(v_a_2006_, 2);
v___x_2135_ = l_Lean_Name_str___override(v_pre_2008_, v___x_2013_);
v___x_2136_ = l_Lean_Expr_const___override(v___x_2135_, v_us_2009_);
v___x_2137_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2136_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref(v___x_2136_);
v___y_1976_ = v___x_2137_;
goto v___jp_1975_;
}
}
}
else
{
lean_dec(v_fst_1964_);
if (lean_obj_tag(v_us_2009_) == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = lean_box(0);
v___x_2139_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1965_, v___x_1971_, v_a_2006_, v___f_1997_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2138_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v___y_1976_ = v___x_2139_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_inc(v_us_2009_);
lean_inc(v_pre_2008_);
lean_dec_ref_known(v_a_2006_, 2);
v___x_2140_ = l_Lean_Name_str___override(v_pre_2008_, v___x_2011_);
v___x_2141_ = l_Lean_Expr_const___override(v___x_2140_, v_us_2009_);
v___x_2142_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v___x_2141_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref(v___x_2141_);
v___y_1976_ = v___x_2142_;
goto v___jp_1975_;
}
}
}
else
{
lean_object* v___x_2143_; 
lean_dec(v_fst_1964_);
v___x_2143_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v_a_2006_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref_known(v_a_2006_, 2);
v___y_1976_ = v___x_2143_;
goto v___jp_1975_;
}
}
else
{
lean_object* v___x_2144_; 
lean_dec(v_fst_1964_);
v___x_2144_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v_a_2006_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref_known(v_a_2006_, 2);
v___y_1976_ = v___x_2144_;
goto v___jp_1975_;
}
}
else
{
lean_object* v___x_2145_; 
lean_dec(v_fst_1964_);
v___x_2145_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1997_, v_fst_1965_, v_fst_1966_, v_fst_1967_, v_fst_1968_, v_snd_1969_, v_a_2006_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v_a_2006_);
v___y_1976_ = v___x_2145_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec_ref(v___f_1997_);
lean_dec_ref(v___x_1974_);
lean_dec(v_snd_1969_);
lean_dec(v_fst_1968_);
lean_dec(v_fst_1967_);
lean_dec(v_fst_1966_);
lean_dec(v_fst_1965_);
lean_dec(v_fst_1964_);
v_a_2146_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2005_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2005_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v___f_1997_);
lean_dec_ref(v___x_1974_);
lean_dec(v_snd_1969_);
lean_dec(v_fst_1968_);
lean_dec(v_fst_1967_);
lean_dec(v_fst_1966_);
lean_dec(v_fst_1965_);
lean_dec(v_fst_1964_);
v_a_2154_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2003_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2003_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref(v___f_1997_);
lean_dec_ref(v___x_1974_);
lean_dec(v_snd_1969_);
lean_dec(v_fst_1968_);
lean_dec(v_fst_1967_);
lean_dec(v_fst_1966_);
lean_dec(v_fst_1965_);
lean_dec(v_fst_1964_);
v_a_2162_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2001_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2001_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec_ref(v___f_1997_);
lean_dec_ref(v___x_1974_);
lean_dec(v_snd_1969_);
lean_dec(v_fst_1968_);
lean_dec(v_fst_1967_);
lean_dec(v_fst_1966_);
lean_dec(v_fst_1965_);
lean_dec(v_fst_1964_);
v_a_2170_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_1999_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_1999_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
v___jp_1975_:
{
if (lean_obj_tag(v___y_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1987_; 
v_a_1977_ = lean_ctor_get(v___y_1976_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___y_1976_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1979_ = v___y_1976_;
v_isShared_1980_ = v_isSharedCheck_1987_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___y_1976_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1987_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
if (lean_obj_tag(v_a_1977_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1983_; 
lean_dec_ref(v___x_1974_);
v_a_1981_ = lean_ctor_get(v_a_1977_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v_a_1977_, 1);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v_a_1981_);
v___x_1983_ = v___x_1979_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
else
{
lean_object* v_a_1985_; 
lean_del_object(v___x_1979_);
v_a_1985_ = lean_ctor_get(v_a_1977_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v_a_1977_, 1);
v_a_1945_ = v___x_1974_;
v_b_1946_ = v_a_1985_;
goto _start;
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v___x_1974_);
v_a_1988_ = lean_ctor_get(v___y_1976_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___y_1976_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___y_1976_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___y_1976_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___boxed(lean_object* v_a_2180_, lean_object* v_b_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v_a_2180_, v_b_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
return v_res_2187_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = lean_unsigned_to_nat(1u);
v___x_2189_ = l_Lean_Compiler_LCNF_spillLinkIdx;
v___x_2190_ = lean_nat_add(v___x_2189_, v___x_2188_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1(lean_object* v_ctorName_2191_, lean_object* v_cidx_2192_, lean_object* v_numFields_2193_, lean_object* v_numParams_2194_, uint8_t v___x_2195_, lean_object* v___f_2196_, lean_object* v_params_2197_, lean_object* v_x_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v_fields_2207_; lean_object* v_nextOffset_2208_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2212_ = lean_mk_empty_array_with_capacity(v_numFields_2193_);
v___x_2213_ = lean_unsigned_to_nat(0u);
v___x_2214_ = lean_nat_add(v_numParams_2194_, v_numFields_2193_);
v___x_2215_ = l_Array_toSubarray___redArg(v_params_2197_, v_numParams_2194_, v___x_2214_);
v___x_2216_ = lean_box(v___x_2195_);
v___x_2217_ = lean_box(v___x_2195_);
v___x_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2216_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = lean_box(v___x_2195_);
v___x_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set(v___x_2220_, 1, v___x_2218_);
v___x_2221_ = lean_box(v___x_2195_);
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v___x_2220_);
v___x_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2213_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2212_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v___x_2215_, v___x_2224_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v_snd_2227_; lean_object* v_snd_2228_; lean_object* v_fst_2229_; lean_object* v_fst_2230_; lean_object* v_fst_2231_; lean_object* v_snd_2232_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v_fields_2236_; lean_object* v_nextOffset_2237_; lean_object* v_fst_2243_; lean_object* v_snd_2244_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v_fields_2248_; lean_object* v_nextOffset_2249_; lean_object* v_fst_2255_; lean_object* v_snd_2256_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v_fields_2260_; lean_object* v_nextOffset_2261_; lean_object* v_fields_2268_; lean_object* v_nextIdx_2269_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2226_);
lean_dec_ref_known(v___x_2225_, 1);
v_snd_2227_ = lean_ctor_get(v_a_2226_, 1);
lean_inc(v_snd_2227_);
v_snd_2228_ = lean_ctor_get(v_snd_2227_, 1);
lean_inc(v_snd_2228_);
v_fst_2229_ = lean_ctor_get(v_a_2226_, 0);
lean_inc(v_fst_2229_);
lean_dec(v_a_2226_);
v_fst_2230_ = lean_ctor_get(v_snd_2227_, 0);
lean_inc(v_fst_2230_);
lean_dec(v_snd_2227_);
v_fst_2231_ = lean_ctor_get(v_snd_2228_, 0);
lean_inc(v_fst_2231_);
v_snd_2232_ = lean_ctor_get(v_snd_2228_, 1);
lean_inc(v_snd_2232_);
lean_dec(v_snd_2228_);
v_fst_2243_ = lean_ctor_get(v_snd_2232_, 0);
lean_inc(v_fst_2243_);
v_snd_2244_ = lean_ctor_get(v_snd_2232_, 1);
lean_inc(v_snd_2244_);
lean_dec(v_snd_2232_);
v_fst_2255_ = lean_ctor_get(v_snd_2244_, 0);
lean_inc(v_fst_2255_);
v_snd_2256_ = lean_ctor_get(v_snd_2244_, 1);
lean_inc(v_snd_2256_);
lean_dec(v_snd_2244_);
v___x_2281_ = l_Lean_Compiler_LCNF_numSpillObjs(v_fst_2230_);
v___x_2282_ = lean_nat_dec_lt(v___x_2213_, v___x_2281_);
lean_dec(v___x_2281_);
if (v___x_2282_ == 0)
{
v_fields_2268_ = v_fst_2229_;
v_nextIdx_2269_ = v_fst_2230_;
goto v___jp_2267_;
}
else
{
size_t v_sz_2283_; size_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
lean_dec(v_fst_2230_);
v_sz_2283_ = lean_array_size(v_fst_2229_);
v___x_2284_ = ((size_t)0ULL);
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5(v_sz_2283_, v___x_2284_, v_fst_2229_);
v___x_2286_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___closed__0, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___closed__0);
v_fields_2268_ = v___x_2285_;
v_nextIdx_2269_ = v___x_2286_;
goto v___jp_2267_;
}
v___jp_2233_:
{
uint8_t v___x_2238_; 
v___x_2238_ = lean_unbox(v_fst_2231_);
lean_dec(v_fst_2231_);
if (v___x_2238_ == 0)
{
lean_dec_ref(v___f_2196_);
v___y_2205_ = v___y_2234_;
v___y_2206_ = v___y_2235_;
v_fields_2207_ = v_fields_2236_;
v_nextOffset_2208_ = v_nextOffset_2237_;
goto v___jp_2204_;
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v_fst_2241_; lean_object* v_snd_2242_; 
v___x_2239_ = lean_unsigned_to_nat(1u);
v___x_2240_ = lean_apply_3(v___f_2196_, v_fields_2236_, v___x_2239_, v_nextOffset_2237_);
v_fst_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_fst_2241_);
v_snd_2242_ = lean_ctor_get(v___x_2240_, 1);
lean_inc(v_snd_2242_);
lean_dec_ref(v___x_2240_);
v___y_2205_ = v___y_2234_;
v___y_2206_ = v___y_2235_;
v_fields_2207_ = v_fst_2241_;
v_nextOffset_2208_ = v_snd_2242_;
goto v___jp_2204_;
}
}
v___jp_2245_:
{
uint8_t v___x_2250_; 
v___x_2250_ = lean_unbox(v_fst_2243_);
lean_dec(v_fst_2243_);
if (v___x_2250_ == 0)
{
v___y_2234_ = v___y_2246_;
v___y_2235_ = v___y_2247_;
v_fields_2236_ = v_fields_2248_;
v_nextOffset_2237_ = v_nextOffset_2249_;
goto v___jp_2233_;
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v_fst_2253_; lean_object* v_snd_2254_; 
v___x_2251_ = lean_unsigned_to_nat(2u);
lean_inc_ref(v___f_2196_);
v___x_2252_ = lean_apply_3(v___f_2196_, v_fields_2248_, v___x_2251_, v_nextOffset_2249_);
v_fst_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_fst_2253_);
v_snd_2254_ = lean_ctor_get(v___x_2252_, 1);
lean_inc(v_snd_2254_);
lean_dec_ref(v___x_2252_);
v___y_2234_ = v___y_2246_;
v___y_2235_ = v___y_2247_;
v_fields_2236_ = v_fst_2253_;
v_nextOffset_2237_ = v_snd_2254_;
goto v___jp_2233_;
}
}
v___jp_2257_:
{
uint8_t v___x_2262_; 
v___x_2262_ = lean_unbox(v_fst_2255_);
lean_dec(v_fst_2255_);
if (v___x_2262_ == 0)
{
v___y_2246_ = v___y_2258_;
v___y_2247_ = v___y_2259_;
v_fields_2248_ = v_fields_2260_;
v_nextOffset_2249_ = v_nextOffset_2261_;
goto v___jp_2245_;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v_fst_2265_; lean_object* v_snd_2266_; 
v___x_2263_ = lean_unsigned_to_nat(4u);
lean_inc_ref(v___f_2196_);
v___x_2264_ = lean_apply_3(v___f_2196_, v_fields_2260_, v___x_2263_, v_nextOffset_2261_);
v_fst_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_fst_2265_);
v_snd_2266_ = lean_ctor_get(v___x_2264_, 1);
lean_inc(v_snd_2266_);
lean_dec_ref(v___x_2264_);
v___y_2246_ = v___y_2258_;
v___y_2247_ = v___y_2259_;
v_fields_2248_ = v_fst_2265_;
v_nextOffset_2249_ = v_snd_2266_;
goto v___jp_2245_;
}
}
v___jp_2267_:
{
size_t v_sz_2270_; size_t v___x_2271_; lean_object* v___x_2272_; lean_object* v_fst_2273_; lean_object* v_snd_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v_sz_2270_ = lean_array_size(v_fields_2268_);
v___x_2271_ = ((size_t)0ULL);
lean_inc(v_nextIdx_2269_);
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(v_sz_2270_, v___x_2271_, v_fields_2268_, v_nextIdx_2269_);
v_fst_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_fst_2273_);
v_snd_2274_ = lean_ctor_get(v___x_2272_, 1);
lean_inc(v_snd_2274_);
lean_dec_ref(v___x_2272_);
v___x_2275_ = lean_nat_sub(v_snd_2274_, v_nextIdx_2269_);
lean_dec(v_snd_2274_);
v___x_2276_ = lean_unbox(v_snd_2256_);
lean_dec(v_snd_2256_);
if (v___x_2276_ == 0)
{
v___y_2258_ = v___x_2275_;
v___y_2259_ = v_nextIdx_2269_;
v_fields_2260_ = v_fst_2273_;
v_nextOffset_2261_ = v___x_2213_;
goto v___jp_2257_;
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v_fst_2279_; lean_object* v_snd_2280_; 
v___x_2277_ = lean_unsigned_to_nat(8u);
lean_inc_ref(v___f_2196_);
v___x_2278_ = lean_apply_3(v___f_2196_, v_fst_2273_, v___x_2277_, v___x_2213_);
v_fst_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_fst_2279_);
v_snd_2280_ = lean_ctor_get(v___x_2278_, 1);
lean_inc(v_snd_2280_);
lean_dec_ref(v___x_2278_);
v___y_2258_ = v___x_2275_;
v___y_2259_ = v_nextIdx_2269_;
v_fields_2260_ = v_fst_2279_;
v_nextOffset_2261_ = v_snd_2280_;
goto v___jp_2257_;
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref(v___f_2196_);
lean_dec(v_cidx_2192_);
lean_dec(v_ctorName_2191_);
v_a_2287_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2225_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2225_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
v___jp_2204_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2209_, 0, v_ctorName_2191_);
lean_ctor_set(v___x_2209_, 1, v_cidx_2192_);
lean_ctor_set(v___x_2209_, 2, v___y_2206_);
lean_ctor_set(v___x_2209_, 3, v___y_2205_);
lean_ctor_set(v___x_2209_, 4, v_nextOffset_2208_);
v___x_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v_fields_2207_);
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___boxed(lean_object* v_ctorName_2295_, lean_object* v_cidx_2296_, lean_object* v_numFields_2297_, lean_object* v_numParams_2298_, lean_object* v___x_2299_, lean_object* v___f_2300_, lean_object* v_params_2301_, lean_object* v_x_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
uint8_t v___x_14437__boxed_2308_; lean_object* v_res_2309_; 
v___x_14437__boxed_2308_ = lean_unbox(v___x_2299_);
v_res_2309_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1(v_ctorName_2295_, v_cidx_2296_, v_numFields_2297_, v_numParams_2298_, v___x_14437__boxed_2308_, v___f_2300_, v_params_2301_, v_x_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec_ref(v_x_2302_);
lean_dec(v_numFields_2297_);
return v_res_2309_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2310_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_2311_ = lean_unsigned_to_nat(66u);
v___x_2312_ = lean_unsigned_to_nat(227u);
v___x_2313_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0));
v___x_2314_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_2315_ = l_mkPanicMessageWithDecl(v___x_2314_, v___x_2313_, v___x_2312_, v___x_2311_, v___x_2310_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(lean_object* v_ctorName_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___f_2326_; lean_object* v___x_2327_; lean_object* v_env_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; 
v___f_2326_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__1));
v___x_2327_ = lean_st_ref_get(v_a_2319_);
v_env_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc_ref(v_env_2328_);
lean_dec(v___x_2327_);
v___x_2329_ = 0;
lean_inc(v_ctorName_2317_);
v___x_2330_ = l_Lean_Environment_find_x3f(v_env_2328_, v_ctorName_2317_, v___x_2329_);
if (lean_obj_tag(v___x_2330_) == 1)
{
lean_object* v_val_2331_; 
v_val_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_val_2331_);
lean_dec_ref_known(v___x_2330_, 1);
if (lean_obj_tag(v_val_2331_) == 6)
{
lean_object* v_val_2332_; lean_object* v_toConstantVal_2333_; lean_object* v_cidx_2334_; lean_object* v_numParams_2335_; lean_object* v_numFields_2336_; lean_object* v_type_2337_; lean_object* v___x_2338_; lean_object* v___f_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v_val_2332_ = lean_ctor_get(v_val_2331_, 0);
lean_inc_ref(v_val_2332_);
lean_dec_ref_known(v_val_2331_, 1);
v_toConstantVal_2333_ = lean_ctor_get(v_val_2332_, 0);
lean_inc_ref(v_toConstantVal_2333_);
v_cidx_2334_ = lean_ctor_get(v_val_2332_, 2);
lean_inc(v_cidx_2334_);
v_numParams_2335_ = lean_ctor_get(v_val_2332_, 3);
lean_inc(v_numParams_2335_);
v_numFields_2336_ = lean_ctor_get(v_val_2332_, 4);
lean_inc(v_numFields_2336_);
lean_dec_ref(v_val_2332_);
v_type_2337_ = lean_ctor_get(v_toConstantVal_2333_, 2);
lean_inc_ref(v_type_2337_);
lean_dec_ref(v_toConstantVal_2333_);
v___x_2338_ = lean_box(v___x_2329_);
v___f_2339_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___boxed), 13, 6);
lean_closure_set(v___f_2339_, 0, v_ctorName_2317_);
lean_closure_set(v___f_2339_, 1, v_cidx_2334_);
lean_closure_set(v___f_2339_, 2, v_numFields_2336_);
lean_closure_set(v___f_2339_, 3, v_numParams_2335_);
lean_closure_set(v___f_2339_, 4, v___x_2338_);
lean_closure_set(v___f_2339_, 5, v___f_2326_);
v___x_2340_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13);
v___x_2341_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17);
v___x_2342_ = lean_st_mk_ref(v___x_2341_);
v___x_2343_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__6___redArg(v_type_2337_, v___f_2339_, v___x_2329_, v___x_2329_, v___x_2340_, v___x_2342_, v_a_2318_, v_a_2319_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2352_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2346_ = v___x_2343_;
v_isShared_2347_ = v_isSharedCheck_2352_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2352_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2348_ = lean_st_ref_get(v___x_2342_);
lean_dec(v___x_2342_);
lean_dec(v___x_2348_);
if (v_isShared_2347_ == 0)
{
v___x_2350_ = v___x_2346_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2344_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
else
{
lean_dec(v___x_2342_);
return v___x_2343_;
}
}
else
{
lean_dec(v_val_2331_);
lean_dec(v_ctorName_2317_);
v___y_2322_ = v_a_2318_;
v___y_2323_ = v_a_2319_;
goto v___jp_2321_;
}
}
else
{
lean_dec(v___x_2330_);
lean_dec(v_ctorName_2317_);
v___y_2322_ = v_a_2318_;
v___y_2323_ = v_a_2319_;
goto v___jp_2321_;
}
v___jp_2321_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0);
v___x_2325_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(v___x_2324_, v___y_2322_, v___y_2323_);
return v___x_2325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___boxed(lean_object* v_ctorName_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(v_ctorName_2353_, v_a_2354_, v_a_2355_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3(lean_object* v_inst_2358_, lean_object* v_R_2359_, lean_object* v_a_2360_, lean_object* v_b_2361_, lean_object* v_c_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v_a_2360_, v_b_2361_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___boxed(lean_object* v_inst_2369_, lean_object* v_R_2370_, lean_object* v_a_2371_, lean_object* v_b_2372_, lean_object* v_c_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3(v_inst_2369_, v_R_2370_, v_a_2371_, v_b_2372_, v_c_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setCtorLayout(lean_object* v_ctorName_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v_env_2386_; lean_object* v___x_2387_; lean_object* v_toEnvExtension_2388_; lean_object* v_asyncMode_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; 
v___x_2384_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
v___x_2385_ = lean_st_ref_get(v_a_2382_);
v_env_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc_ref(v_env_2386_);
lean_dec(v___x_2385_);
v___x_2387_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt;
v_toEnvExtension_2388_ = lean_ctor_get(v___x_2387_, 0);
v_asyncMode_2389_ = lean_ctor_get(v_toEnvExtension_2388_, 2);
v___x_2390_ = 0;
lean_inc(v_ctorName_2380_);
v___x_2391_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2384_, v___x_2387_, v_env_2386_, v_ctorName_2380_, v_asyncMode_2389_, v___x_2390_);
if (lean_obj_tag(v___x_2391_) == 0)
{
uint8_t v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = 0;
lean_inc(v_ctorName_2380_);
v___x_2393_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(v_ctorName_2380_, v_a_2381_, v_a_2382_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2395_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc_n(v_a_2394_, 2);
lean_dec_ref_known(v___x_2393_, 1);
v___x_2395_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout(v_a_2394_, v_a_2381_, v_a_2382_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2424_; 
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2424_ == 0)
{
lean_object* v_unused_2425_; 
v_unused_2425_ = lean_ctor_get(v___x_2395_, 0);
lean_dec(v_unused_2425_);
v___x_2397_ = v___x_2395_;
v_isShared_2398_ = v_isSharedCheck_2424_;
goto v_resetjp_2396_;
}
else
{
lean_dec(v___x_2395_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2424_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v_env_2400_; lean_object* v_nextMacroScope_2401_; lean_object* v_ngen_2402_; lean_object* v_auxDeclNGen_2403_; lean_object* v_traceState_2404_; lean_object* v_recordedDeps_2405_; lean_object* v_messages_2406_; lean_object* v_infoState_2407_; lean_object* v_snapshotTasks_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2422_; 
v___x_2399_ = lean_st_ref_take(v_a_2382_);
v_env_2400_ = lean_ctor_get(v___x_2399_, 0);
v_nextMacroScope_2401_ = lean_ctor_get(v___x_2399_, 1);
v_ngen_2402_ = lean_ctor_get(v___x_2399_, 2);
v_auxDeclNGen_2403_ = lean_ctor_get(v___x_2399_, 3);
v_traceState_2404_ = lean_ctor_get(v___x_2399_, 4);
v_recordedDeps_2405_ = lean_ctor_get(v___x_2399_, 6);
v_messages_2406_ = lean_ctor_get(v___x_2399_, 7);
v_infoState_2407_ = lean_ctor_get(v___x_2399_, 8);
v_snapshotTasks_2408_ = lean_ctor_get(v___x_2399_, 9);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2422_ == 0)
{
lean_object* v_unused_2423_; 
v_unused_2423_ = lean_ctor_get(v___x_2399_, 5);
lean_dec(v_unused_2423_);
v___x_2410_ = v___x_2399_;
v_isShared_2411_ = v_isSharedCheck_2422_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_snapshotTasks_2408_);
lean_inc(v_infoState_2407_);
lean_inc(v_messages_2406_);
lean_inc(v_recordedDeps_2405_);
lean_inc(v_traceState_2404_);
lean_inc(v_auxDeclNGen_2403_);
lean_inc(v_ngen_2402_);
lean_inc(v_nextMacroScope_2401_);
lean_inc(v_env_2400_);
lean_dec(v___x_2399_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2422_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2412_ = lean_box(0);
v___x_2413_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2387_, v_env_2400_, v_ctorName_2380_, v_a_2394_, v___x_2392_);
v___x_2414_ = lean_obj_once(&l_Lean_Compiler_LCNF_setImpureType___closed__1, &l_Lean_Compiler_LCNF_setImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_setImpureType___closed__1);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 5, v___x_2414_);
lean_ctor_set(v___x_2410_, 0, v___x_2413_);
v___x_2416_ = v___x_2410_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_nextMacroScope_2401_);
lean_ctor_set(v_reuseFailAlloc_2421_, 2, v_ngen_2402_);
lean_ctor_set(v_reuseFailAlloc_2421_, 3, v_auxDeclNGen_2403_);
lean_ctor_set(v_reuseFailAlloc_2421_, 4, v_traceState_2404_);
lean_ctor_set(v_reuseFailAlloc_2421_, 5, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2421_, 6, v_recordedDeps_2405_);
lean_ctor_set(v_reuseFailAlloc_2421_, 7, v_messages_2406_);
lean_ctor_set(v_reuseFailAlloc_2421_, 8, v_infoState_2407_);
lean_ctor_set(v_reuseFailAlloc_2421_, 9, v_snapshotTasks_2408_);
v___x_2416_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2417_ = lean_st_ref_put(v_a_2382_, v___x_2416_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2412_);
v___x_2419_ = v___x_2397_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2412_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
else
{
lean_dec(v_a_2394_);
lean_dec(v_ctorName_2380_);
return v___x_2395_;
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v_ctorName_2380_);
v_a_2426_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2393_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2393_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
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
else
{
lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2441_; 
lean_dec(v_ctorName_2380_);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; 
v_unused_2442_ = lean_ctor_get(v___x_2391_, 0);
lean_dec(v_unused_2442_);
v___x_2435_ = v___x_2391_;
v_isShared_2436_ = v_isSharedCheck_2441_;
goto v_resetjp_2434_;
}
else
{
lean_dec(v___x_2391_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2441_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2437_ = lean_box(0);
if (v_isShared_2436_ == 0)
{
lean_ctor_set_tag(v___x_2435_, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2437_);
v___x_2439_ = v___x_2435_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setCtorLayout___boxed(lean_object* v_ctorName_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_Compiler_LCNF_setCtorLayout(v_ctorName_2443_, v_a_2444_, v_a_2445_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getCtorLayout(lean_object* v_ctorName_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v_env_2454_; lean_object* v___x_2455_; lean_object* v_toEnvExtension_2456_; lean_object* v_asyncMode_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; 
v___x_2452_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
v___x_2453_ = lean_st_ref_get(v_a_2450_);
v_env_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc_ref(v_env_2454_);
lean_dec(v___x_2453_);
v___x_2455_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt;
v_toEnvExtension_2456_ = lean_ctor_get(v___x_2455_, 0);
v_asyncMode_2457_ = lean_ctor_get(v_toEnvExtension_2456_, 2);
v___x_2458_ = 0;
lean_inc(v_ctorName_2448_);
v___x_2459_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2452_, v___x_2455_, v_env_2454_, v_ctorName_2448_, v_asyncMode_2457_, v___x_2458_);
if (lean_obj_tag(v___x_2459_) == 1)
{
lean_object* v_val_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec(v_ctorName_2448_);
v_val_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_val_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
lean_ctor_set_tag(v___x_2462_, 0);
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_val_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
else
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_dec(v___x_2459_);
v___x_2468_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__1, &l_Lean_Compiler_LCNF_nameToImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1);
v___x_2469_ = l_Lean_MessageData_ofName(v_ctorName_2448_);
v___x_2470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2468_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__3, &l_Lean_Compiler_LCNF_nameToImpureType___closed__3_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__3);
v___x_2472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v___x_2472_, v_a_2449_, v_a_2450_);
return v___x_2473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getCtorLayout___boxed(lean_object* v_ctorName_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_2474_, v_a_2475_, v_a_2476_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(lean_object* v_as_2479_, size_t v_sz_2480_, size_t v_i_2481_, lean_object* v_b_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
uint8_t v___x_2486_; 
v___x_2486_ = lean_usize_dec_lt(v_i_2481_, v_sz_2480_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v_b_2482_);
return v___x_2487_;
}
else
{
lean_object* v___x_2488_; lean_object* v_a_2489_; lean_object* v___x_2490_; 
v___x_2488_ = lean_box(0);
v_a_2489_ = lean_array_uget_borrowed(v_as_2479_, v_i_2481_);
lean_inc(v_a_2489_);
v___x_2490_ = l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(v_a_2489_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v___x_2491_; 
lean_dec_ref_known(v___x_2490_, 1);
lean_inc(v_a_2489_);
v___x_2491_ = l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f(v_a_2489_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2491_) == 0)
{
size_t v___x_2492_; size_t v___x_2493_; 
lean_dec_ref_known(v___x_2491_, 1);
v___x_2492_ = ((size_t)1ULL);
v___x_2493_ = lean_usize_add(v_i_2481_, v___x_2492_);
v_i_2481_ = v___x_2493_;
v_b_2482_ = v___x_2488_;
goto _start;
}
else
{
return v___x_2491_;
}
}
else
{
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2___boxed(lean_object* v_as_2495_, lean_object* v_sz_2496_, lean_object* v_i_2497_, lean_object* v_b_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
size_t v_sz_boxed_2502_; size_t v_i_boxed_2503_; lean_object* v_res_2504_; 
v_sz_boxed_2502_ = lean_unbox_usize(v_sz_2496_);
lean_dec(v_sz_2496_);
v_i_boxed_2503_ = lean_unbox_usize(v_i_2497_);
lean_dec(v_i_2497_);
v_res_2504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(v_as_2495_, v_sz_boxed_2502_, v_i_boxed_2503_, v_b_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec_ref(v_as_2495_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(lean_object* v_as_x27_2505_, lean_object* v_b_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
if (lean_obj_tag(v_as_x27_2505_) == 0)
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_b_2506_);
return v___x_2510_;
}
else
{
lean_object* v_head_2511_; lean_object* v_tail_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v_head_2511_ = lean_ctor_get(v_as_x27_2505_, 0);
v_tail_2512_ = lean_ctor_get(v_as_x27_2505_, 1);
v___x_2513_ = lean_box(0);
lean_inc(v_head_2511_);
v___x_2514_ = l_Lean_Compiler_LCNF_setOtherDeclMonoType(v_head_2511_, v___y_2507_, v___y_2508_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v___x_2515_; 
lean_dec_ref_known(v___x_2514_, 1);
lean_inc(v_head_2511_);
v___x_2515_ = l_Lean_Compiler_LCNF_setCtorLayout(v_head_2511_, v___y_2507_, v___y_2508_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_dec_ref_known(v___x_2515_, 1);
v_as_x27_2505_ = v_tail_2512_;
v_b_2506_ = v___x_2513_;
goto _start;
}
else
{
return v___x_2515_;
}
}
else
{
return v___x_2514_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg___boxed(lean_object* v_as_x27_2517_, lean_object* v_b_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(v_as_x27_2517_, v_b_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v_as_x27_2517_);
return v_res_2522_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_2525_ = l_Lean_stringToMessageData(v___x_2524_);
return v___x_2525_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_2528_ = l_Lean_stringToMessageData(v___x_2527_);
return v___x_2528_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_2531_ = l_Lean_stringToMessageData(v___x_2530_);
return v___x_2531_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_2534_ = l_Lean_stringToMessageData(v___x_2533_);
return v___x_2534_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_2537_ = l_Lean_stringToMessageData(v___x_2536_);
return v___x_2537_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_2540_ = l_Lean_stringToMessageData(v___x_2539_);
return v___x_2540_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_2543_ = l_Lean_stringToMessageData(v___x_2542_);
return v___x_2543_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_2546_ = l_Lean_stringToMessageData(v___x_2545_);
return v___x_2546_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_2549_ = l_Lean_stringToMessageData(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_2552_ = l_Lean_stringToMessageData(v___x_2551_);
return v___x_2552_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__21(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__20));
v___x_2555_ = l_Lean_stringToMessageData(v___x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2556_, lean_object* v_declHint_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v_env_2562_; uint8_t v___x_2563_; 
v___x_2560_ = lean_box(0);
v___x_2561_ = lean_st_ref_get(v___y_2558_);
v_env_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc_ref(v_env_2562_);
lean_dec(v___x_2561_);
v___x_2563_ = l_Lean_Name_isAnonymous(v_declHint_2557_);
if (v___x_2563_ == 0)
{
uint8_t v_isExporting_2564_; 
v_isExporting_2564_ = lean_ctor_get_uint8(v_env_2562_, sizeof(void*)*13);
if (v_isExporting_2564_ == 0)
{
lean_object* v___x_2565_; 
lean_dec_ref(v_env_2562_);
lean_dec(v_declHint_2557_);
v___x_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2565_, 0, v_msg_2556_);
return v___x_2565_;
}
else
{
lean_object* v___x_2566_; uint8_t v___x_2567_; 
lean_inc_ref(v_env_2562_);
v___x_2566_ = l_Lean_Environment_setExporting(v_env_2562_, v___x_2563_);
lean_inc(v_declHint_2557_);
lean_inc_ref(v___x_2566_);
v___x_2567_ = l_Lean_Environment_contains(v___x_2566_, v_declHint_2557_, v_isExporting_2564_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; 
lean_dec_ref(v___x_2566_);
lean_dec_ref(v_env_2562_);
lean_dec(v_declHint_2557_);
v___x_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2568_, 0, v_msg_2556_);
return v___x_2568_;
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v_c_2574_; lean_object* v___x_2575_; 
v___x_2569_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1);
v___x_2570_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2);
v___x_2571_ = l_Lean_Options_empty;
v___x_2572_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2566_);
lean_ctor_set(v___x_2572_, 1, v___x_2569_);
lean_ctor_set(v___x_2572_, 2, v___x_2570_);
lean_ctor_set(v___x_2572_, 3, v___x_2571_);
lean_inc(v_declHint_2557_);
v___x_2573_ = l_Lean_MessageData_ofConstName(v_declHint_2557_, v___x_2563_);
v_c_2574_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2574_, 0, v___x_2572_);
lean_ctor_set(v_c_2574_, 1, v___x_2573_);
v___x_2575_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2562_, v_declHint_2557_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
lean_dec_ref(v_env_2562_);
lean_dec(v_declHint_2557_);
v___x_2576_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v_c_2574_);
v___x_2578_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = l_Lean_MessageData_note(v___x_2579_);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v_msg_2556_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
return v___x_2582_;
}
else
{
lean_object* v_val_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2639_; 
v_val_2583_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2585_ = v___x_2575_;
v_isShared_2586_ = v_isSharedCheck_2639_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_val_2583_);
lean_dec(v___x_2575_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2639_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v_modules_2588_; lean_object* v_moduleNames_2589_; lean_object* v_mod_2590_; uint8_t v___y_2592_; uint8_t v___x_2622_; 
v___x_2587_ = l_Lean_Environment_header(v_env_2562_);
lean_dec_ref(v_env_2562_);
v_modules_2588_ = lean_ctor_get(v___x_2587_, 3);
lean_inc_ref(v_modules_2588_);
v_moduleNames_2589_ = lean_ctor_get(v___x_2587_, 4);
lean_inc_ref(v_moduleNames_2589_);
lean_dec_ref(v___x_2587_);
v_mod_2590_ = lean_array_get(v___x_2560_, v_moduleNames_2589_, v_val_2583_);
lean_dec_ref(v_moduleNames_2589_);
v___x_2622_ = l_Lean_isPrivateName(v_declHint_2557_);
lean_dec(v_declHint_2557_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2623_ = lean_array_get_size(v_modules_2588_);
v___x_2624_ = lean_nat_dec_lt(v_val_2583_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_dec_ref(v_modules_2588_);
lean_dec(v_val_2583_);
v___y_2592_ = v___x_2622_;
goto v___jp_2591_;
}
else
{
lean_object* v___x_2625_; lean_object* v_toImport_2626_; uint8_t v_isExported_2627_; 
v___x_2625_ = lean_array_fget(v_modules_2588_, v_val_2583_);
lean_dec(v_val_2583_);
lean_dec_ref(v_modules_2588_);
v_toImport_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc_ref(v_toImport_2626_);
lean_dec(v___x_2625_);
v_isExported_2627_ = lean_ctor_get_uint8(v_toImport_2626_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2626_);
v___y_2592_ = v_isExported_2627_;
goto v___jp_2591_;
}
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_dec_ref(v_modules_2588_);
lean_del_object(v___x_2585_);
lean_dec(v_val_2583_);
v___x_2628_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
lean_ctor_set(v___x_2629_, 1, v_c_2574_);
v___x_2630_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_2631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2629_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = l_Lean_MessageData_ofName(v_mod_2590_);
v___x_2633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2631_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__21);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = l_Lean_MessageData_note(v___x_2635_);
v___x_2637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2637_, 0, v_msg_2556_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
return v___x_2638_;
}
v___jp_2591_:
{
if (v___y_2592_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
v___x_2593_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_2594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v_c_2574_);
v___x_2595_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_2596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2594_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = l_Lean_MessageData_ofName(v_mod_2590_);
v___x_2598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2596_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_2600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2598_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = l_Lean_MessageData_note(v___x_2600_);
v___x_2602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2602_, 0, v_msg_2556_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2602_);
v___x_2604_ = v___x_2585_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
else
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2620_; 
v___x_2606_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
lean_ctor_set(v___x_2607_, 1, v_c_2574_);
v___x_2608_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_2609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2607_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = l_Lean_MessageData_ofName(v_mod_2590_);
lean_inc_ref(v___x_2610_);
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2609_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_2613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2611_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
lean_ctor_set(v___x_2614_, 1, v___x_2610_);
v___x_2615_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_2616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2614_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = l_Lean_MessageData_note(v___x_2616_);
v___x_2618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2618_, 0, v_msg_2556_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2618_);
v___x_2620_ = v___x_2585_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
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
lean_object* v___x_2640_; 
lean_dec_ref(v_env_2562_);
lean_dec(v_declHint_2557_);
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v_msg_2556_);
return v___x_2640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2641_, lean_object* v_declHint_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_2641_, v_declHint_2642_, v___y_2643_);
lean_dec(v___y_2643_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(lean_object* v_msg_2646_, lean_object* v_declHint_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2661_; 
v___x_2651_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_2646_, v_declHint_2647_, v___y_2649_);
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2654_ = v___x_2651_;
v_isShared_2655_ = v_isSharedCheck_2661_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2651_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2661_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2656_ = l_Lean_unknownIdentifierMessageTag;
v___x_2657_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
lean_ctor_set(v___x_2657_, 1, v_a_2652_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___x_2657_);
v___x_2659_ = v___x_2654_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8___boxed(lean_object* v_msg_2662_, lean_object* v_declHint_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_2662_, v_declHint_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(lean_object* v_ref_2668_, lean_object* v_msg_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_toCold_2673_; lean_object* v_currRecDepth_2674_; lean_object* v_ref_2675_; uint16_t v_optionFlags_2676_; uint8_t v_suppressElabErrors_2677_; uint8_t v_isRecordingDeps_2678_; lean_object* v_ref_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v_toCold_2673_ = lean_ctor_get(v___y_2670_, 0);
v_currRecDepth_2674_ = lean_ctor_get(v___y_2670_, 1);
v_ref_2675_ = lean_ctor_get(v___y_2670_, 2);
v_optionFlags_2676_ = lean_ctor_get_uint16(v___y_2670_, sizeof(void*)*3);
v_suppressElabErrors_2677_ = lean_ctor_get_uint8(v___y_2670_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2678_ = lean_ctor_get_uint8(v___y_2670_, sizeof(void*)*3 + 3);
v_ref_2679_ = l_Lean_replaceRef(v_ref_2668_, v_ref_2675_);
lean_inc(v_currRecDepth_2674_);
lean_inc_ref(v_toCold_2673_);
v___x_2680_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2680_, 0, v_toCold_2673_);
lean_ctor_set(v___x_2680_, 1, v_currRecDepth_2674_);
lean_ctor_set(v___x_2680_, 2, v_ref_2679_);
lean_ctor_set_uint16(v___x_2680_, sizeof(void*)*3, v_optionFlags_2676_);
lean_ctor_set_uint8(v___x_2680_, sizeof(void*)*3 + 2, v_suppressElabErrors_2677_);
lean_ctor_set_uint8(v___x_2680_, sizeof(void*)*3 + 3, v_isRecordingDeps_2678_);
v___x_2681_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_msg_2669_, v___x_2680_, v___y_2671_);
lean_dec_ref_known(v___x_2680_, 3);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2682_, lean_object* v_msg_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_2682_, v_msg_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v_ref_2682_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(lean_object* v_ref_2688_, lean_object* v_msg_2689_, lean_object* v_declHint_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v___x_2694_; lean_object* v_a_2695_; lean_object* v___x_2696_; 
v___x_2694_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_2689_, v_declHint_2690_, v___y_2691_, v___y_2692_);
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref(v___x_2694_);
v___x_2696_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_2688_, v_a_2695_, v___y_2691_, v___y_2692_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2697_, lean_object* v_msg_2698_, lean_object* v_declHint_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_2697_, v_msg_2698_, v_declHint_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v_ref_2697_);
return v_res_2703_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2706_ = l_Lean_stringToMessageData(v___x_2705_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2707_, lean_object* v_constName_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___x_2712_; uint8_t v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2712_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2713_ = 0;
lean_inc(v_constName_2708_);
v___x_2714_ = l_Lean_MessageData_ofConstName(v_constName_2708_, v___x_2713_);
v___x_2715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2712_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__1, &l_Lean_Compiler_LCNF_nameToImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1);
v___x_2717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_2707_, v___x_2717_, v_constName_2708_, v___y_2709_, v___y_2710_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2719_, lean_object* v_constName_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(v_ref_2719_, v_constName_2720_, v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v_ref_2719_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(lean_object* v_constName_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_ref_2729_; lean_object* v___x_2730_; 
v_ref_2729_ = lean_ctor_get(v___y_2726_, 2);
v___x_2730_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(v_ref_2729_, v_constName_2725_, v___y_2726_, v___y_2727_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(v_constName_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0(lean_object* v_constName_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; lean_object* v_env_2741_; uint8_t v___x_2742_; lean_object* v___x_2743_; 
v___x_2740_ = lean_st_ref_get(v___y_2738_);
v_env_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc_ref(v_env_2741_);
lean_dec(v___x_2740_);
v___x_2742_ = 0;
lean_inc(v_constName_2736_);
v___x_2743_ = l_Lean_Environment_find_x3f(v_env_2741_, v_constName_2736_, v___x_2742_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(v_constName_2736_, v___y_2737_, v___y_2738_);
return v___x_2744_;
}
else
{
lean_object* v_val_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec(v_constName_2736_);
v_val_2745_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2743_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_val_2745_);
lean_dec(v___x_2743_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
lean_ctor_set_tag(v___x_2747_, 0);
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_val_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0___boxed(lean_object* v_constName_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0(v_constName_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
return v_res_2757_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2759_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_2760_ = lean_unsigned_to_nat(49u);
v___x_2761_ = lean_unsigned_to_nat(338u);
v___x_2762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__0));
v___x_2763_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_2764_ = l_mkPanicMessageWithDecl(v___x_2763_, v___x_2762_, v___x_2761_, v___x_2760_, v___x_2759_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4(lean_object* v_as_2765_, size_t v_sz_2766_, size_t v_i_2767_, lean_object* v_b_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v_a_2773_; uint8_t v___x_2777_; 
v___x_2777_ = lean_usize_dec_lt(v_i_2767_, v_sz_2766_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2778_, 0, v_b_2768_);
return v___x_2778_;
}
else
{
lean_object* v___x_2779_; lean_object* v_a_2780_; lean_object* v___x_2781_; 
v___x_2779_ = lean_box(0);
v_a_2780_ = lean_array_uget_borrowed(v_as_2765_, v_i_2767_);
lean_inc(v_a_2780_);
v___x_2781_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0(v_a_2780_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2781_, 1);
if (lean_obj_tag(v_a_2782_) == 5)
{
lean_object* v_val_2783_; lean_object* v_ctors_2784_; lean_object* v___x_2785_; 
v_val_2783_ = lean_ctor_get(v_a_2782_, 0);
lean_inc_ref(v_val_2783_);
lean_dec_ref_known(v_a_2782_, 1);
v_ctors_2784_ = lean_ctor_get(v_val_2783_, 4);
lean_inc(v_ctors_2784_);
lean_dec_ref(v_val_2783_);
v___x_2785_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(v_ctors_2784_, v___x_2779_, v___y_2769_, v___y_2770_);
lean_dec(v_ctors_2784_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_dec_ref_known(v___x_2785_, 1);
v_a_2773_ = v___x_2779_;
goto v___jp_2772_;
}
else
{
return v___x_2785_;
}
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_dec(v_a_2782_);
v___x_2786_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1);
v___x_2787_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(v___x_2786_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_dec_ref_known(v___x_2787_, 1);
v_a_2773_ = v___x_2779_;
goto v___jp_2772_;
}
else
{
return v___x_2787_;
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
v_a_2788_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2781_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2781_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
v___jp_2772_:
{
size_t v___x_2774_; size_t v___x_2775_; 
v___x_2774_ = ((size_t)1ULL);
v___x_2775_ = lean_usize_add(v_i_2767_, v___x_2774_);
v_i_2767_ = v___x_2775_;
v_b_2768_ = v_a_2773_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___boxed(lean_object* v_as_2796_, lean_object* v_sz_2797_, lean_object* v_i_2798_, lean_object* v_b_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
size_t v_sz_boxed_2803_; size_t v_i_boxed_2804_; lean_object* v_res_2805_; 
v_sz_boxed_2803_ = lean_unbox_usize(v_sz_2797_);
lean_dec(v_sz_2797_);
v_i_boxed_2804_ = lean_unbox_usize(v_i_2798_);
lean_dec(v_i_2798_);
v_res_2805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4(v_as_2796_, v_sz_boxed_2803_, v_i_boxed_2804_, v_b_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec_ref(v_as_2796_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3(lean_object* v_as_2806_, size_t v_sz_2807_, size_t v_i_2808_, lean_object* v_b_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
uint8_t v___x_2813_; 
v___x_2813_ = lean_usize_dec_lt(v_i_2808_, v_sz_2807_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; 
v___x_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2814_, 0, v_b_2809_);
return v___x_2814_;
}
else
{
lean_object* v___x_2815_; lean_object* v_a_2816_; lean_object* v___x_2817_; 
v___x_2815_ = lean_box(0);
v_a_2816_ = lean_array_uget_borrowed(v_as_2806_, v_i_2808_);
lean_inc(v_a_2816_);
v___x_2817_ = l_Lean_Compiler_LCNF_setOtherDeclMonoType(v_a_2816_, v___y_2810_, v___y_2811_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v___x_2818_; 
lean_dec_ref_known(v___x_2817_, 1);
lean_inc(v_a_2816_);
v___x_2818_ = l_Lean_Compiler_LCNF_setImpureType(v_a_2816_, v___y_2810_, v___y_2811_);
if (lean_obj_tag(v___x_2818_) == 0)
{
size_t v___x_2819_; size_t v___x_2820_; 
lean_dec_ref_known(v___x_2818_, 1);
v___x_2819_ = ((size_t)1ULL);
v___x_2820_ = lean_usize_add(v_i_2808_, v___x_2819_);
v_i_2808_ = v___x_2820_;
v_b_2809_ = v___x_2815_;
goto _start;
}
else
{
return v___x_2818_;
}
}
else
{
return v___x_2817_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3___boxed(lean_object* v_as_2822_, lean_object* v_sz_2823_, lean_object* v_i_2824_, lean_object* v_b_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
size_t v_sz_boxed_2829_; size_t v_i_boxed_2830_; lean_object* v_res_2831_; 
v_sz_boxed_2829_ = lean_unbox_usize(v_sz_2823_);
lean_dec(v_sz_2823_);
v_i_boxed_2830_ = lean_unbox_usize(v_i_2824_);
lean_dec(v_i_2824_);
v_res_2831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3(v_as_2822_, v_sz_boxed_2829_, v_i_boxed_2830_, v_b_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec_ref(v_as_2822_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(lean_object* v_as_2832_, size_t v_i_2833_, size_t v_stop_2834_, lean_object* v_b_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_a_2839_; uint8_t v___x_2843_; 
v___x_2843_ = lean_usize_dec_eq(v_i_2833_, v_stop_2834_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v_env_2846_; lean_object* v___x_2847_; 
v___x_2844_ = lean_array_uget_borrowed(v_as_2832_, v_i_2833_);
v___x_2845_ = lean_st_ref_get(v___y_2836_);
v_env_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc_ref(v_env_2846_);
lean_dec(v___x_2845_);
lean_inc(v___x_2844_);
v___x_2847_ = l_Lean_Environment_find_x3f(v_env_2846_, v___x_2844_, v___x_2843_);
if (lean_obj_tag(v___x_2847_) == 1)
{
lean_object* v_val_2848_; 
v_val_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_val_2848_);
lean_dec_ref_known(v___x_2847_, 1);
if (lean_obj_tag(v_val_2848_) == 5)
{
lean_object* v___x_2849_; 
lean_dec_ref_known(v_val_2848_, 1);
lean_inc(v___x_2844_);
v___x_2849_ = lean_array_push(v_b_2835_, v___x_2844_);
v_a_2839_ = v___x_2849_;
goto v___jp_2838_;
}
else
{
lean_dec(v_val_2848_);
v_a_2839_ = v_b_2835_;
goto v___jp_2838_;
}
}
else
{
lean_dec(v___x_2847_);
v_a_2839_ = v_b_2835_;
goto v___jp_2838_;
}
}
else
{
lean_object* v___x_2850_; 
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v_b_2835_);
return v___x_2850_;
}
v___jp_2838_:
{
size_t v___x_2840_; size_t v___x_2841_; 
v___x_2840_ = ((size_t)1ULL);
v___x_2841_ = lean_usize_add(v_i_2833_, v___x_2840_);
v_i_2833_ = v___x_2841_;
v_b_2835_ = v_a_2839_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg___boxed(lean_object* v_as_2851_, lean_object* v_i_2852_, lean_object* v_stop_2853_, lean_object* v_b_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
size_t v_i_boxed_2857_; size_t v_stop_boxed_2858_; lean_object* v_res_2859_; 
v_i_boxed_2857_ = lean_unbox_usize(v_i_2852_);
lean_dec(v_i_2852_);
v_stop_boxed_2858_ = lean_unbox_usize(v_stop_2853_);
lean_dec(v_stop_2853_);
v_res_2859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_as_2851_, v_i_boxed_2857_, v_stop_boxed_2858_, v_b_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v_as_2851_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compileInductives(lean_object* v_typeNames_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v_a_2867_; lean_object* v___y_2883_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; uint8_t v___x_2896_; 
v___x_2893_ = lean_unsigned_to_nat(0u);
v___x_2894_ = lean_array_get_size(v_typeNames_2862_);
v___x_2895_ = ((lean_object*)(l_Lean_Compiler_LCNF_compileInductives___closed__0));
v___x_2896_ = lean_nat_dec_lt(v___x_2893_, v___x_2894_);
if (v___x_2896_ == 0)
{
v_a_2867_ = v___x_2895_;
goto v___jp_2866_;
}
else
{
uint8_t v___x_2897_; 
v___x_2897_ = lean_nat_dec_le(v___x_2894_, v___x_2894_);
if (v___x_2897_ == 0)
{
if (v___x_2896_ == 0)
{
v_a_2867_ = v___x_2895_;
goto v___jp_2866_;
}
else
{
size_t v___x_2898_; size_t v___x_2899_; lean_object* v___x_2900_; 
v___x_2898_ = ((size_t)0ULL);
v___x_2899_ = lean_usize_of_nat(v___x_2894_);
v___x_2900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_typeNames_2862_, v___x_2898_, v___x_2899_, v___x_2895_, v_a_2864_);
v___y_2883_ = v___x_2900_;
goto v___jp_2882_;
}
}
else
{
size_t v___x_2901_; size_t v___x_2902_; lean_object* v___x_2903_; 
v___x_2901_ = ((size_t)0ULL);
v___x_2902_ = lean_usize_of_nat(v___x_2894_);
v___x_2903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_typeNames_2862_, v___x_2901_, v___x_2902_, v___x_2895_, v_a_2864_);
v___y_2883_ = v___x_2903_;
goto v___jp_2882_;
}
}
v___jp_2866_:
{
lean_object* v___x_2868_; size_t v_sz_2869_; size_t v___x_2870_; lean_object* v___x_2871_; 
v___x_2868_ = lean_box(0);
v_sz_2869_ = lean_array_size(v_a_2867_);
v___x_2870_ = ((size_t)0ULL);
v___x_2871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(v_a_2867_, v_sz_2869_, v___x_2870_, v___x_2868_, v_a_2863_, v_a_2864_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v___x_2872_; 
lean_dec_ref_known(v___x_2871_, 1);
v___x_2872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3(v_a_2867_, v_sz_2869_, v___x_2870_, v___x_2868_, v_a_2863_, v_a_2864_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v___x_2873_; 
lean_dec_ref_known(v___x_2872_, 1);
v___x_2873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4(v_a_2867_, v_sz_2869_, v___x_2870_, v___x_2868_, v_a_2863_, v_a_2864_);
lean_dec_ref(v_a_2867_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2880_ == 0)
{
lean_object* v_unused_2881_; 
v_unused_2881_ = lean_ctor_get(v___x_2873_, 0);
lean_dec(v_unused_2881_);
v___x_2875_ = v___x_2873_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_dec(v___x_2873_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2868_);
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2868_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
else
{
return v___x_2873_;
}
}
else
{
lean_dec_ref(v_a_2867_);
return v___x_2872_;
}
}
else
{
lean_dec_ref(v_a_2867_);
return v___x_2871_;
}
}
v___jp_2882_:
{
if (lean_obj_tag(v___y_2883_) == 0)
{
lean_object* v_a_2884_; 
v_a_2884_ = lean_ctor_get(v___y_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___y_2883_, 1);
v_a_2867_ = v_a_2884_;
goto v___jp_2866_;
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
v_a_2885_ = lean_ctor_get(v___y_2883_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___y_2883_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___y_2883_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___y_2883_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compileInductives___boxed(lean_object* v_typeNames_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_Compiler_LCNF_compileInductives(v_typeNames_2904_, v_a_2905_, v_a_2906_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec_ref(v_typeNames_2904_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1(lean_object* v_as_2909_, lean_object* v_as_x27_2910_, lean_object* v_b_2911_, lean_object* v_a_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(v_as_x27_2910_, v_b_2911_, v___y_2913_, v___y_2914_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___boxed(lean_object* v_as_2917_, lean_object* v_as_x27_2918_, lean_object* v_b_2919_, lean_object* v_a_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1(v_as_2917_, v_as_x27_2918_, v_b_2919_, v_a_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v_as_x27_2918_);
lean_dec(v_as_2917_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5(lean_object* v_as_2925_, size_t v_i_2926_, size_t v_stop_2927_, lean_object* v_b_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_as_2925_, v_i_2926_, v_stop_2927_, v_b_2928_, v___y_2930_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___boxed(lean_object* v_as_2933_, lean_object* v_i_2934_, lean_object* v_stop_2935_, lean_object* v_b_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
size_t v_i_boxed_2940_; size_t v_stop_boxed_2941_; lean_object* v_res_2942_; 
v_i_boxed_2940_ = lean_unbox_usize(v_i_2934_);
lean_dec(v_i_2934_);
v_stop_boxed_2941_ = lean_unbox_usize(v_stop_2935_);
lean_dec(v_stop_2935_);
v_res_2942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5(v_as_2933_, v_i_boxed_2940_, v_stop_boxed_2941_, v_b_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec_ref(v_as_2933_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0(lean_object* v_00_u03b1_2943_, lean_object* v_constName_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(v_constName_2944_, v___y_2945_, v___y_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2949_, lean_object* v_constName_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0(v_00_u03b1_2949_, v_constName_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2955_, lean_object* v_ref_2956_, lean_object* v_constName_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(v_ref_2956_, v_constName_2957_, v___y_2958_, v___y_2959_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2962_, lean_object* v_ref_2963_, lean_object* v_constName_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1(v_00_u03b1_2962_, v_ref_2963_, v_constName_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v_ref_2963_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b1_2969_, lean_object* v_ref_2970_, lean_object* v_msg_2971_, lean_object* v_declHint_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_2970_, v_msg_2971_, v_declHint_2972_, v___y_2973_, v___y_2974_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___boxed(lean_object* v_00_u03b1_2977_, lean_object* v_ref_2978_, lean_object* v_msg_2979_, lean_object* v_declHint_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7(v_00_u03b1_2977_, v_ref_2978_, v_msg_2979_, v_declHint_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v_ref_2978_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(lean_object* v_msg_2985_, lean_object* v_declHint_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_2985_, v_declHint_2986_, v___y_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2991_, lean_object* v_declHint_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(v_msg_2991_, v_declHint_2992_, v___y_2993_, v___y_2994_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_2997_, lean_object* v_ref_2998_, lean_object* v_msg_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_2998_, v_msg_2999_, v___y_3000_, v___y_3001_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3004_, lean_object* v_ref_3005_, lean_object* v_msg_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9(v_00_u03b1_3004_, v_ref_3005_, v_msg_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v_ref_3005_);
return v_res_3010_;
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
