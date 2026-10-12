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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCtorInfo_default;
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
v___x_756_ = lean_unsigned_to_nat(92u);
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
v___x_1209_ = lean_unsigned_to_nat(138u);
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
v___x_1215_ = lean_unsigned_to_nat(150u);
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
default: 
{
lean_dec(v_t_1296_);
return v_k_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim(lean_object* v_motive_1307_, lean_object* v_ctorIdx_1308_, lean_object* v_t_1309_, lean_object* v_h_1310_, lean_object* v_k_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1309_, v_k_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___boxed(lean_object* v_motive_1313_, lean_object* v_ctorIdx_1314_, lean_object* v_t_1315_, lean_object* v_h_1316_, lean_object* v_k_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim(v_motive_1313_, v_ctorIdx_1314_, v_t_1315_, v_h_1316_, v_k_1317_);
lean_dec(v_ctorIdx_1314_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_erased_elim___redArg(lean_object* v_t_1319_, lean_object* v_erased_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1319_, v_erased_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_erased_elim(lean_object* v_motive_1322_, lean_object* v_t_1323_, lean_object* v_h_1324_, lean_object* v_erased_1325_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1323_, v_erased_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_object_elim___redArg(lean_object* v_t_1327_, lean_object* v_object_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1327_, v_object_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_object_elim(lean_object* v_motive_1330_, lean_object* v_t_1331_, lean_object* v_h_1332_, lean_object* v_object_1333_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1331_, v_object_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_usize_elim___redArg(lean_object* v_t_1335_, lean_object* v_usize_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1335_, v_usize_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_usize_elim(lean_object* v_motive_1338_, lean_object* v_t_1339_, lean_object* v_h_1340_, lean_object* v_usize_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1339_, v_usize_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_scalar_elim___redArg(lean_object* v_t_1343_, lean_object* v_scalar_1344_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1343_, v_scalar_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_scalar_elim(lean_object* v_motive_1346_, lean_object* v_t_1347_, lean_object* v_h_1348_, lean_object* v_scalar_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1347_, v_scalar_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_void_elim___redArg(lean_object* v_t_1351_, lean_object* v_void_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1351_, v_void_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_void_elim(lean_object* v_motive_1354_, lean_object* v_t_1355_, lean_object* v_h_1356_, lean_object* v_void_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_1355_, v_void_1357_);
return v___x_1358_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo_default(void){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_box(0);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo(void){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_box(0);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format(lean_object* v_x_1382_){
_start:
{
switch(lean_obj_tag(v_x_1382_))
{
case 0:
{
lean_object* v___x_1383_; 
v___x_1383_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__1));
return v___x_1383_;
}
case 1:
{
lean_object* v_i_1384_; lean_object* v_type_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1400_; 
v_i_1384_ = lean_ctor_get(v_x_1382_, 0);
v_type_1385_ = lean_ctor_get(v_x_1382_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1387_ = v_x_1382_;
v_isShared_1388_ = v_isSharedCheck_1400_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_type_1385_);
lean_inc(v_i_1384_);
lean_dec(v_x_1382_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1400_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1389_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__3));
v___x_1390_ = l_Nat_reprFast(v_i_1384_);
v___x_1391_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set_tag(v___x_1387_, 5);
lean_ctor_set(v___x_1387_, 1, v___x_1391_);
lean_ctor_set(v___x_1387_, 0, v___x_1389_);
v___x_1393_ = v___x_1387_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1394_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5));
v___x_1395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1393_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v___x_1396_ = lean_expr_dbg_to_string(v_type_1385_);
lean_dec_ref(v_type_1385_);
v___x_1397_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
v___x_1398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1395_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
return v___x_1398_;
}
}
}
case 2:
{
lean_object* v_i_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1411_; 
v_i_1401_ = lean_ctor_get(v_x_1382_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1403_ = v_x_1382_;
v_isShared_1404_ = v_isSharedCheck_1411_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_i_1401_);
lean_dec(v_x_1382_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1411_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1405_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__7));
v___x_1406_ = l_Nat_reprFast(v_i_1401_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set_tag(v___x_1403_, 3);
lean_ctor_set(v___x_1403_, 0, v___x_1406_);
v___x_1408_ = v___x_1403_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; 
v___x_1409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1405_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
return v___x_1409_;
}
}
}
case 3:
{
lean_object* v_sz_1412_; lean_object* v_offset_1413_; lean_object* v_type_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_sz_1412_ = lean_ctor_get(v_x_1382_, 0);
lean_inc(v_sz_1412_);
v_offset_1413_ = lean_ctor_get(v_x_1382_, 1);
lean_inc(v_offset_1413_);
v_type_1414_ = lean_ctor_get(v_x_1382_, 2);
lean_inc_ref(v_type_1414_);
lean_dec_ref_known(v_x_1382_, 3);
v___x_1415_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__9));
v___x_1416_ = l_Nat_reprFast(v_sz_1412_);
v___x_1417_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
v___x_1418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1415_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__11));
v___x_1420_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = l_Nat_reprFast(v_offset_1413_);
v___x_1422_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
v___x_1423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1420_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5));
v___x_1425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
v___x_1426_ = lean_expr_dbg_to_string(v_type_1414_);
lean_dec_ref(v_type_1414_);
v___x_1427_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
v___x_1428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1425_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
return v___x_1428_;
}
default: 
{
lean_object* v___x_1429_; 
v___x_1429_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__13));
return v___x_1429_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0));
v___x_1435_ = l_Lean_Compiler_LCNF_instInhabitedCtorInfo_default;
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
lean_ctor_set(v___x_1436_, 1, v___x_1434_);
return v___x_1436_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default(void){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1);
return v___x_1437_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout(void){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_init_1439_, lean_object* v_x_1440_){
_start:
{
if (lean_obj_tag(v_x_1440_) == 0)
{
lean_object* v_k_1441_; lean_object* v_v_1442_; lean_object* v_l_1443_; lean_object* v_r_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_k_1441_ = lean_ctor_get(v_x_1440_, 1);
v_v_1442_ = lean_ctor_get(v_x_1440_, 2);
v_l_1443_ = lean_ctor_get(v_x_1440_, 3);
v_r_1444_ = lean_ctor_get(v_x_1440_, 4);
v___x_1445_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(v_init_1439_, v_l_1443_);
lean_inc(v_v_1442_);
lean_inc(v_k_1441_);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v_k_1441_);
lean_ctor_set(v___x_1446_, 1, v_v_1442_);
v___x_1447_ = lean_array_push(v___x_1445_, v___x_1446_);
v_init_1439_ = v___x_1447_;
v_x_1440_ = v_r_1444_;
goto _start;
}
else
{
return v_init_1439_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_init_1449_, lean_object* v_x_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(v_init_1449_, v_x_1450_);
lean_dec(v_x_1450_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2(lean_object* v_env_1452_, lean_object* v_as_1453_, size_t v_i_1454_, size_t v_stop_1455_, lean_object* v_b_1456_){
_start:
{
lean_object* v___y_1458_; uint8_t v___x_1462_; 
v___x_1462_ = lean_usize_dec_eq(v_i_1454_, v_stop_1455_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v_fst_1464_; uint8_t v___x_1465_; 
v___x_1463_ = lean_array_uget_borrowed(v_as_1453_, v_i_1454_);
v_fst_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_fst_1464_);
lean_inc_ref(v_env_1452_);
v___x_1465_ = l_Lean_Environment_contains(v_env_1452_, v_fst_1464_, v___x_1462_);
if (v___x_1465_ == 0)
{
v___y_1458_ = v_b_1456_;
goto v___jp_1457_;
}
else
{
lean_object* v___x_1466_; 
lean_inc(v___x_1463_);
v___x_1466_ = lean_array_push(v_b_1456_, v___x_1463_);
v___y_1458_ = v___x_1466_;
goto v___jp_1457_;
}
}
else
{
lean_dec_ref(v_env_1452_);
return v_b_1456_;
}
v___jp_1457_:
{
size_t v___x_1459_; size_t v___x_1460_; 
v___x_1459_ = ((size_t)1ULL);
v___x_1460_ = lean_usize_add(v_i_1454_, v___x_1459_);
v_i_1454_ = v___x_1460_;
v_b_1456_ = v___y_1458_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_1467_, lean_object* v_as_1468_, lean_object* v_i_1469_, lean_object* v_stop_1470_, lean_object* v_b_1471_){
_start:
{
size_t v_i_boxed_1472_; size_t v_stop_boxed_1473_; lean_object* v_res_1474_; 
v_i_boxed_1472_ = lean_unbox_usize(v_i_1469_);
lean_dec(v_i_1469_);
v_stop_boxed_1473_ = lean_unbox_usize(v_stop_1470_);
lean_dec(v_stop_1470_);
v_res_1474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2(v_env_1467_, v_as_1468_, v_i_boxed_1472_, v_stop_boxed_1473_, v_b_1471_);
lean_dec_ref(v_as_1468_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(lean_object* v_env_1475_, lean_object* v_as_1476_, size_t v_i_1477_, size_t v_stop_1478_, lean_object* v_b_1479_){
_start:
{
lean_object* v___y_1481_; uint8_t v___x_1485_; 
v___x_1485_ = lean_usize_dec_eq(v_i_1477_, v_stop_1478_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v_fst_1487_; uint8_t v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1486_ = lean_array_uget_borrowed(v_as_1476_, v_i_1477_);
v_fst_1487_ = lean_ctor_get(v___x_1486_, 0);
v___x_1488_ = 1;
lean_inc_ref(v_env_1475_);
v___x_1489_ = l_Lean_Environment_setExporting(v_env_1475_, v___x_1488_);
lean_inc(v_fst_1487_);
v___x_1490_ = l_Lean_Environment_contains(v___x_1489_, v_fst_1487_, v___x_1488_);
if (v___x_1490_ == 0)
{
v___y_1481_ = v_b_1479_;
goto v___jp_1480_;
}
else
{
lean_object* v___x_1491_; 
lean_inc(v___x_1486_);
v___x_1491_ = lean_array_push(v_b_1479_, v___x_1486_);
v___y_1481_ = v___x_1491_;
goto v___jp_1480_;
}
}
else
{
lean_dec_ref(v_env_1475_);
return v_b_1479_;
}
v___jp_1480_:
{
size_t v___x_1482_; size_t v___x_1483_; 
v___x_1482_ = ((size_t)1ULL);
v___x_1483_ = lean_usize_add(v_i_1477_, v___x_1482_);
v_i_1477_ = v___x_1483_;
v_b_1479_ = v___y_1481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_1492_, lean_object* v_as_1493_, lean_object* v_i_1494_, lean_object* v_stop_1495_, lean_object* v_b_1496_){
_start:
{
size_t v_i_boxed_1497_; size_t v_stop_boxed_1498_; lean_object* v_res_1499_; 
v_i_boxed_1497_ = lean_unbox_usize(v_i_1494_);
lean_dec(v_i_1494_);
v_stop_boxed_1498_ = lean_unbox_usize(v_stop_1495_);
lean_dec(v_stop_1495_);
v_res_1499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(v_env_1492_, v_as_1493_, v_i_boxed_1497_, v_stop_boxed_1498_, v_b_1496_);
lean_dec_ref(v_as_1493_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(lean_object* v___x_1500_, lean_object* v_env_1501_, lean_object* v_s_1502_){
_start:
{
lean_object* v___y_1504_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1519_ = lean_mk_empty_array_with_capacity(v___x_1500_);
v___x_1520_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(v___x_1519_, v_s_1502_);
v___x_1521_ = lean_array_get_size(v___x_1520_);
v___x_1522_ = lean_mk_empty_array_with_capacity(v___x_1500_);
v___x_1523_ = lean_nat_dec_lt(v___x_1500_, v___x_1521_);
if (v___x_1523_ == 0)
{
lean_dec_ref(v___x_1520_);
v___y_1504_ = v___x_1522_;
goto v___jp_1503_;
}
else
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_nat_dec_le(v___x_1521_, v___x_1521_);
if (v___x_1524_ == 0)
{
if (v___x_1523_ == 0)
{
lean_dec_ref(v___x_1520_);
v___y_1504_ = v___x_1522_;
goto v___jp_1503_;
}
else
{
size_t v___x_1525_; size_t v___x_1526_; lean_object* v___x_1527_; 
v___x_1525_ = ((size_t)0ULL);
v___x_1526_ = lean_usize_of_nat(v___x_1521_);
lean_inc_ref(v_env_1501_);
v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2(v_env_1501_, v___x_1520_, v___x_1525_, v___x_1526_, v___x_1522_);
lean_dec_ref(v___x_1520_);
v___y_1504_ = v___x_1527_;
goto v___jp_1503_;
}
}
else
{
size_t v___x_1528_; size_t v___x_1529_; lean_object* v___x_1530_; 
v___x_1528_ = ((size_t)0ULL);
v___x_1529_ = lean_usize_of_nat(v___x_1521_);
lean_inc_ref(v_env_1501_);
v___x_1530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__2(v_env_1501_, v___x_1520_, v___x_1528_, v___x_1529_, v___x_1522_);
lean_dec_ref(v___x_1520_);
v___y_1504_ = v___x_1530_;
goto v___jp_1503_;
}
}
v___jp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1505_ = lean_array_get_size(v___y_1504_);
v___x_1506_ = lean_mk_empty_array_with_capacity(v___x_1500_);
v___x_1507_ = lean_nat_dec_lt(v___x_1500_, v___x_1505_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
lean_dec_ref(v_env_1501_);
lean_inc_ref(v___x_1506_);
v___x_1508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set(v___x_1508_, 1, v___x_1506_);
lean_ctor_set(v___x_1508_, 2, v___y_1504_);
return v___x_1508_;
}
else
{
uint8_t v___x_1509_; 
v___x_1509_ = lean_nat_dec_le(v___x_1505_, v___x_1505_);
if (v___x_1509_ == 0)
{
if (v___x_1507_ == 0)
{
lean_object* v___x_1510_; 
lean_dec_ref(v_env_1501_);
lean_inc_ref(v___x_1506_);
v___x_1510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1506_);
lean_ctor_set(v___x_1510_, 1, v___x_1506_);
lean_ctor_set(v___x_1510_, 2, v___y_1504_);
return v___x_1510_;
}
else
{
size_t v___x_1511_; size_t v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1511_ = ((size_t)0ULL);
v___x_1512_ = lean_usize_of_nat(v___x_1505_);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(v_env_1501_, v___y_1504_, v___x_1511_, v___x_1512_, v___x_1506_);
lean_inc_ref(v___x_1513_);
v___x_1514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
lean_ctor_set(v___x_1514_, 2, v___y_1504_);
return v___x_1514_;
}
}
else
{
size_t v___x_1515_; size_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1515_ = ((size_t)0ULL);
v___x_1516_ = lean_usize_of_nat(v___x_1505_);
v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__0(v_env_1501_, v___y_1504_, v___x_1515_, v___x_1516_, v___x_1506_);
lean_inc_ref(v___x_1517_);
v___x_1518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
lean_ctor_set(v___x_1518_, 2, v___y_1504_);
return v___x_1518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2____boxed(lean_object* v___x_1531_, lean_object* v_env_1532_, lean_object* v_s_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(v___x_1531_, v_env_1532_, v_s_1533_);
lean_dec(v_s_1533_);
lean_dec(v___x_1531_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; lean_object* v___x_1546_; 
v___f_1542_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_));
v___x_1543_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_));
v___x_1544_ = lean_box(0);
v___x_1545_ = 0;
v___x_1546_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_1543_, v___x_1544_, v___x_1545_, v___f_1542_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2____boxed(lean_object* v_a_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2_();
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(lean_object* v_init_1549_, lean_object* v_t_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1_spec__1(v_init_1549_, v_t_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1___boxed(lean_object* v_init_1552_, lean_object* v_t_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1917064764____hygCtx___hyg_2__spec__1(v_init_1552_, v_t_1553_);
lean_dec(v_t_1553_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout(lean_object* v_layout_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_ctorInfo_1559_; lean_object* v___x_1560_; 
v_ctorInfo_1559_ = lean_ctor_get(v_layout_1555_, 0);
lean_inc_ref(v_ctorInfo_1559_);
lean_dec_ref(v_layout_1555_);
v___x_1560_ = l_Lean_Compiler_LCNF_CtorInfo_checkValid(v_ctorInfo_1559_, v_a_1556_, v_a_1557_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout___boxed(lean_object* v_layout_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout(v_layout_1561_, v_a_1562_, v_a_1563_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(lean_object* v_msg_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___f_1570_; lean_object* v___x_11545__overap_1571_; lean_object* v___x_1572_; 
v___f_1570_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0___closed__0));
v___x_11545__overap_1571_ = lean_panic_fn_borrowed(v___f_1570_, v_msg_1566_);
lean_inc(v___y_1568_);
lean_inc_ref(v___y_1567_);
v___x_1572_ = lean_apply_3(v___x_11545__overap_1571_, v___y_1567_, v___y_1568_, lean_box(0));
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1___boxed(lean_object* v_msg_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(v_msg_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(lean_object* v_msg_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___f_1585_; lean_object* v___x_11555__overap_1586_; lean_object* v___x_1587_; 
v___f_1585_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___closed__0));
v___x_11555__overap_1586_ = lean_panic_fn_borrowed(v___f_1585_, v_msg_1579_);
lean_inc(v___y_1583_);
lean_inc_ref(v___y_1582_);
lean_inc(v___y_1581_);
lean_inc_ref(v___y_1580_);
v___x_1587_ = lean_apply_5(v___x_11555__overap_1586_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, lean_box(0));
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2___boxed(lean_object* v_msg_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(v_msg_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg(lean_object* v_type_1595_, lean_object* v_k_1596_, uint8_t v_cleanupAnnotations_1597_, uint8_t v_whnfType_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___f_1604_; lean_object* v___x_1605_; 
v___f_1604_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1604_, 0, v_k_1596_);
v___x_1605_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1595_, v___f_1604_, v_cleanupAnnotations_1597_, v_whnfType_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1605_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1605_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
v_a_1614_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1605_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1605_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg___boxed(lean_object* v_type_1622_, lean_object* v_k_1623_, lean_object* v_cleanupAnnotations_1624_, lean_object* v_whnfType_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1631_; uint8_t v_whnfType_boxed_1632_; lean_object* v_res_1633_; 
v_cleanupAnnotations_boxed_1631_ = lean_unbox(v_cleanupAnnotations_1624_);
v_whnfType_boxed_1632_ = lean_unbox(v_whnfType_1625_);
v_res_1633_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg(v_type_1622_, v_k_1623_, v_cleanupAnnotations_boxed_1631_, v_whnfType_boxed_1632_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5(lean_object* v_00_u03b1_1634_, lean_object* v_type_1635_, lean_object* v_k_1636_, uint8_t v_cleanupAnnotations_1637_, uint8_t v_whnfType_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg(v_type_1635_, v_k_1636_, v_cleanupAnnotations_1637_, v_whnfType_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___boxed(lean_object* v_00_u03b1_1645_, lean_object* v_type_1646_, lean_object* v_k_1647_, lean_object* v_cleanupAnnotations_1648_, lean_object* v_whnfType_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1655_; uint8_t v_whnfType_boxed_1656_; lean_object* v_res_1657_; 
v_cleanupAnnotations_boxed_1655_ = lean_unbox(v_cleanupAnnotations_1648_);
v_whnfType_boxed_1656_ = lean_unbox(v_whnfType_1649_);
v_res_1657_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5(v_00_u03b1_1645_, v_type_1646_, v_k_1647_, v_cleanupAnnotations_boxed_1655_, v_whnfType_boxed_1656_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(lean_object* v_size_1658_, size_t v_sz_1659_, size_t v_i_1660_, lean_object* v_bs_1661_, lean_object* v___y_1662_){
_start:
{
uint8_t v___x_1663_; 
v___x_1663_ = lean_usize_dec_lt(v_i_1660_, v_sz_1659_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v_bs_1661_);
lean_ctor_set(v___x_1664_, 1, v___y_1662_);
return v___x_1664_;
}
else
{
lean_object* v_v_1665_; lean_object* v___x_1666_; lean_object* v_bs_x27_1667_; lean_object* v_fst_1669_; lean_object* v_snd_1670_; 
v_v_1665_ = lean_array_uget(v_bs_1661_, v_i_1660_);
v___x_1666_ = lean_unsigned_to_nat(0u);
v_bs_x27_1667_ = lean_array_uset(v_bs_1661_, v_i_1660_, v___x_1666_);
if (lean_obj_tag(v_v_1665_) == 3)
{
lean_object* v_sz_1675_; lean_object* v_type_1676_; uint8_t v___x_1677_; 
v_sz_1675_ = lean_ctor_get(v_v_1665_, 0);
v_type_1676_ = lean_ctor_get(v_v_1665_, 2);
v___x_1677_ = lean_nat_dec_eq(v_sz_1675_, v_size_1658_);
if (v___x_1677_ == 0)
{
v_fst_1669_ = v_v_1665_;
v_snd_1670_ = v___y_1662_;
goto v___jp_1668_;
}
else
{
lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1685_; 
lean_inc_ref(v_type_1676_);
lean_inc(v_sz_1675_);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_v_1665_);
if (v_isSharedCheck_1685_ == 0)
{
lean_object* v_unused_1686_; lean_object* v_unused_1687_; lean_object* v_unused_1688_; 
v_unused_1686_ = lean_ctor_get(v_v_1665_, 2);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_v_1665_, 1);
lean_dec(v_unused_1687_);
v_unused_1688_ = lean_ctor_get(v_v_1665_, 0);
lean_dec(v_unused_1688_);
v___x_1679_ = v_v_1665_;
v_isShared_1680_ = v_isSharedCheck_1685_;
goto v_resetjp_1678_;
}
else
{
lean_dec(v_v_1665_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1685_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = lean_nat_add(v___y_1662_, v_sz_1675_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v___y_1662_);
v___x_1683_ = v___x_1679_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_sz_1675_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v___y_1662_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_type_1676_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
v_fst_1669_ = v___x_1683_;
v_snd_1670_ = v___x_1681_;
goto v___jp_1668_;
}
}
}
}
else
{
v_fst_1669_ = v_v_1665_;
v_snd_1670_ = v___y_1662_;
goto v___jp_1668_;
}
v___jp_1668_:
{
size_t v___x_1671_; size_t v___x_1672_; lean_object* v___x_1673_; 
v___x_1671_ = ((size_t)1ULL);
v___x_1672_ = lean_usize_add(v_i_1660_, v___x_1671_);
v___x_1673_ = lean_array_uset(v_bs_x27_1667_, v_i_1660_, v_fst_1669_);
v_i_1660_ = v___x_1672_;
v_bs_1661_ = v___x_1673_;
v___y_1662_ = v_snd_1670_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0___boxed(lean_object* v_size_1689_, lean_object* v_sz_1690_, lean_object* v_i_1691_, lean_object* v_bs_1692_, lean_object* v___y_1693_){
_start:
{
size_t v_sz_boxed_1694_; size_t v_i_boxed_1695_; lean_object* v_res_1696_; 
v_sz_boxed_1694_ = lean_unbox_usize(v_sz_1690_);
lean_dec(v_sz_1690_);
v_i_boxed_1695_ = lean_unbox_usize(v_i_1691_);
lean_dec(v_i_1691_);
v_res_1696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(v_size_1689_, v_sz_boxed_1694_, v_i_boxed_1695_, v_bs_1692_, v___y_1693_);
lean_dec(v_size_1689_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0(lean_object* v_fields_1697_, lean_object* v_size_1698_, lean_object* v_nextOffset_1699_){
_start:
{
size_t v_sz_1700_; size_t v___x_1701_; lean_object* v___x_1702_; 
v_sz_1700_ = lean_array_size(v_fields_1697_);
v___x_1701_ = ((size_t)0ULL);
v___x_1702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__0(v_size_1698_, v_sz_1700_, v___x_1701_, v_fields_1697_, v_nextOffset_1699_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0___boxed(lean_object* v_fields_1703_, lean_object* v_size_1704_, lean_object* v_nextOffset_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__0(v_fields_1703_, v_size_1704_, v_nextOffset_1705_);
lean_dec(v_size_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(size_t v_sz_1707_, size_t v_i_1708_, lean_object* v_bs_1709_, lean_object* v___y_1710_){
_start:
{
uint8_t v___x_1711_; 
v___x_1711_ = lean_usize_dec_lt(v_i_1708_, v_sz_1707_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_bs_1709_);
lean_ctor_set(v___x_1712_, 1, v___y_1710_);
return v___x_1712_;
}
else
{
lean_object* v_v_1713_; lean_object* v___x_1714_; lean_object* v_bs_x27_1715_; lean_object* v_fst_1717_; lean_object* v_snd_1718_; 
v_v_1713_ = lean_array_uget(v_bs_1709_, v_i_1708_);
v___x_1714_ = lean_unsigned_to_nat(0u);
v_bs_x27_1715_ = lean_array_uset(v_bs_1709_, v_i_1708_, v___x_1714_);
if (lean_obj_tag(v_v_1713_) == 2)
{
lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1731_; 
v_isSharedCheck_1731_ = !lean_is_exclusive(v_v_1713_);
if (v_isSharedCheck_1731_ == 0)
{
lean_object* v_unused_1732_; 
v_unused_1732_ = lean_ctor_get(v_v_1713_, 0);
lean_dec(v_unused_1732_);
v___x_1724_ = v_v_1713_;
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
else
{
lean_dec(v_v_1713_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1726_ = lean_unsigned_to_nat(1u);
v___x_1727_ = lean_nat_add(v___y_1710_, v___x_1726_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___y_1710_);
v___x_1729_ = v___x_1724_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___y_1710_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
v_fst_1717_ = v___x_1729_;
v_snd_1718_ = v___x_1727_;
goto v___jp_1716_;
}
}
}
else
{
v_fst_1717_ = v_v_1713_;
v_snd_1718_ = v___y_1710_;
goto v___jp_1716_;
}
v___jp_1716_:
{
size_t v___x_1719_; size_t v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = ((size_t)1ULL);
v___x_1720_ = lean_usize_add(v_i_1708_, v___x_1719_);
v___x_1721_ = lean_array_uset(v_bs_x27_1715_, v_i_1708_, v_fst_1717_);
v_i_1708_ = v___x_1720_;
v_bs_1709_ = v___x_1721_;
v___y_1710_ = v_snd_1718_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4___boxed(lean_object* v_sz_1733_, lean_object* v_i_1734_, lean_object* v_bs_1735_, lean_object* v___y_1736_){
_start:
{
size_t v_sz_boxed_1737_; size_t v_i_boxed_1738_; lean_object* v_res_1739_; 
v_sz_boxed_1737_ = lean_unbox_usize(v_sz_1733_);
lean_dec(v_sz_1733_);
v_i_boxed_1738_ = lean_unbox_usize(v_i_1734_);
lean_dec(v_i_1734_);
v_res_1739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(v_sz_boxed_1737_, v_i_boxed_1738_, v_bs_1735_, v___y_1736_);
return v_res_1739_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1741_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_1742_ = lean_unsigned_to_nat(15u);
v___x_1743_ = lean_unsigned_to_nat(238u);
v___x_1744_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0));
v___x_1745_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_1746_ = l_mkPanicMessageWithDecl(v___x_1745_, v___x_1744_, v___x_1743_, v___x_1742_, v___x_1741_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(lean_object* v___f_1747_, lean_object* v_fst_1748_, lean_object* v_fst_1749_, lean_object* v_fst_1750_, lean_object* v_fst_1751_, lean_object* v_snd_1752_, lean_object* v_x_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1);
v___x_1760_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__2(v___x_1759_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1762_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
lean_inc(v___y_1757_);
lean_inc_ref(v___y_1756_);
lean_inc(v___y_1755_);
lean_inc_ref(v___y_1754_);
v___x_1762_ = lean_apply_11(v___f_1747_, v_a_1761_, v_fst_1748_, v_fst_1749_, v_fst_1750_, v_fst_1751_, v_snd_1752_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, lean_box(0));
return v___x_1762_;
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec(v_snd_1752_);
lean_dec(v_fst_1751_);
lean_dec(v_fst_1750_);
lean_dec(v_fst_1749_);
lean_dec(v_fst_1748_);
lean_dec_ref(v___f_1747_);
v_a_1763_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1760_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1760_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___boxed(lean_object* v___f_1771_, lean_object* v_fst_1772_, lean_object* v_fst_1773_, lean_object* v_fst_1774_, lean_object* v_fst_1775_, lean_object* v_snd_1776_, lean_object* v_x_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1771_, v_fst_1772_, v_fst_1773_, v_fst_1774_, v_fst_1775_, v_snd_1776_, v_x_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec_ref(v_x_1777_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(lean_object* v_fst_1784_, lean_object* v_ctorField_1785_, lean_object* v_nextIdx_1786_, uint8_t v_has1BScalar_1787_, uint8_t v_has2BScalar_1788_, uint8_t v_has4BScalar_1789_, uint8_t v_has8BScalar_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1796_ = lean_array_push(v_fst_1784_, v_ctorField_1785_);
v___x_1797_ = lean_box(v_has4BScalar_1789_);
v___x_1798_ = lean_box(v_has8BScalar_1790_);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = lean_box(v_has2BScalar_1788_);
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___x_1799_);
v___x_1802_ = lean_box(v_has1BScalar_1787_);
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
lean_ctor_set(v___x_1803_, 1, v___x_1801_);
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v_nextIdx_1786_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1796_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0___boxed(lean_object* v_fst_1808_, lean_object* v_ctorField_1809_, lean_object* v_nextIdx_1810_, lean_object* v_has1BScalar_1811_, lean_object* v_has2BScalar_1812_, lean_object* v_has4BScalar_1813_, lean_object* v_has8BScalar_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
uint8_t v_has1BScalar_boxed_1820_; uint8_t v_has2BScalar_boxed_1821_; uint8_t v_has4BScalar_boxed_1822_; uint8_t v_has8BScalar_boxed_1823_; lean_object* v_res_1824_; 
v_has1BScalar_boxed_1820_ = lean_unbox(v_has1BScalar_1811_);
v_has2BScalar_boxed_1821_ = lean_unbox(v_has2BScalar_1812_);
v_has4BScalar_boxed_1822_ = lean_unbox(v_has4BScalar_1813_);
v_has8BScalar_boxed_1823_ = lean_unbox(v_has8BScalar_1814_);
v_res_1824_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1808_, v_ctorField_1809_, v_nextIdx_1810_, v_has1BScalar_boxed_1820_, v_has2BScalar_boxed_1821_, v_has4BScalar_boxed_1822_, v_has8BScalar_boxed_1823_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(lean_object* v_fst_1825_, lean_object* v___x_1826_, lean_object* v_a_1827_, lean_object* v___f_1828_, lean_object* v_fst_1829_, lean_object* v_fst_1830_, lean_object* v_fst_1831_, lean_object* v_snd_1832_, lean_object* v_00___1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = lean_nat_add(v_fst_1825_, v___x_1826_);
v___x_1840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_fst_1825_);
lean_ctor_set(v___x_1840_, 1, v_a_1827_);
lean_inc(v___y_1837_);
lean_inc_ref(v___y_1836_);
lean_inc(v___y_1835_);
lean_inc_ref(v___y_1834_);
v___x_1841_ = lean_apply_11(v___f_1828_, v___x_1840_, v___x_1839_, v_fst_1829_, v_fst_1830_, v_fst_1831_, v_snd_1832_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, lean_box(0));
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2___boxed(lean_object* v_fst_1842_, lean_object* v___x_1843_, lean_object* v_a_1844_, lean_object* v___f_1845_, lean_object* v_fst_1846_, lean_object* v_fst_1847_, lean_object* v_fst_1848_, lean_object* v_snd_1849_, lean_object* v_00___1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1842_, v___x_1843_, v_a_1844_, v___f_1845_, v_fst_1846_, v_fst_1847_, v_fst_1848_, v_snd_1849_, v_00___1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___x_1843_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(lean_object* v_a_1859_, lean_object* v_b_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_array_1866_; lean_object* v_start_1867_; lean_object* v_stop_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_2093_; 
v_array_1866_ = lean_ctor_get(v_a_1859_, 0);
v_start_1867_ = lean_ctor_get(v_a_1859_, 1);
v_stop_1868_ = lean_ctor_get(v_a_1859_, 2);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_a_1859_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_1870_ = v_a_1859_;
v_isShared_1871_ = v_isSharedCheck_2093_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_stop_1868_);
lean_inc(v_start_1867_);
lean_inc(v_array_1866_);
lean_dec(v_a_1859_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_2093_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
uint8_t v___x_1872_; 
v___x_1872_ = lean_nat_dec_lt(v_start_1867_, v_stop_1868_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; 
lean_del_object(v___x_1870_);
lean_dec(v_stop_1868_);
lean_dec(v_start_1867_);
lean_dec_ref(v_array_1866_);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v_b_1860_);
return v___x_1873_;
}
else
{
lean_object* v_snd_1874_; lean_object* v_snd_1875_; lean_object* v_snd_1876_; lean_object* v_snd_1877_; lean_object* v_fst_1878_; lean_object* v_fst_1879_; lean_object* v_fst_1880_; lean_object* v_fst_1881_; lean_object* v_fst_1882_; lean_object* v_snd_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v_snd_1874_ = lean_ctor_get(v_b_1860_, 1);
lean_inc(v_snd_1874_);
v_snd_1875_ = lean_ctor_get(v_snd_1874_, 1);
lean_inc(v_snd_1875_);
v_snd_1876_ = lean_ctor_get(v_snd_1875_, 1);
lean_inc(v_snd_1876_);
v_snd_1877_ = lean_ctor_get(v_snd_1876_, 1);
lean_inc(v_snd_1877_);
v_fst_1878_ = lean_ctor_get(v_b_1860_, 0);
lean_inc(v_fst_1878_);
lean_dec_ref(v_b_1860_);
v_fst_1879_ = lean_ctor_get(v_snd_1874_, 0);
lean_inc(v_fst_1879_);
lean_dec(v_snd_1874_);
v_fst_1880_ = lean_ctor_get(v_snd_1875_, 0);
lean_inc(v_fst_1880_);
lean_dec(v_snd_1875_);
v_fst_1881_ = lean_ctor_get(v_snd_1876_, 0);
lean_inc(v_fst_1881_);
lean_dec(v_snd_1876_);
v_fst_1882_ = lean_ctor_get(v_snd_1877_, 0);
lean_inc(v_fst_1882_);
v_snd_1883_ = lean_ctor_get(v_snd_1877_, 1);
lean_inc(v_snd_1883_);
lean_dec(v_snd_1877_);
v___x_1884_ = lean_unsigned_to_nat(0u);
v___x_1885_ = lean_unsigned_to_nat(1u);
v___x_1886_ = lean_nat_add(v_start_1867_, v___x_1885_);
lean_inc_ref(v_array_1866_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 1, v___x_1886_);
v___x_1888_ = v___x_1870_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_array_1866_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_stop_1868_);
v___x_1888_ = v_reuseFailAlloc_2092_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___y_1890_; lean_object* v___x_1910_; lean_object* v___f_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1910_ = lean_array_fget(v_array_1866_, v_start_1867_);
lean_dec(v_start_1867_);
lean_dec_ref(v_array_1866_);
lean_inc(v_fst_1878_);
v___f_1911_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1911_, 0, v_fst_1878_);
v___x_1912_ = l_Lean_Expr_fvarId_x21(v___x_1910_);
lean_dec(v___x_1910_);
v___x_1913_ = l_Lean_FVarId_getType___redArg(v___x_1912_, v___y_1861_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = l_Lean_Compiler_LCNF_toLCNFType(v_a_1914_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
v___x_1917_ = l_Lean_Compiler_LCNF_toMonoType(v_a_1916_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v___x_1919_ = l_Lean_Compiler_LCNF_toImpureType(v_a_1918_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
if (lean_obj_tag(v_a_1920_) == 4)
{
lean_object* v_declName_1921_; 
v_declName_1921_ = lean_ctor_get(v_a_1920_, 0);
if (lean_obj_tag(v_declName_1921_) == 1)
{
lean_object* v_pre_1922_; 
v_pre_1922_ = lean_ctor_get(v_declName_1921_, 0);
if (lean_obj_tag(v_pre_1922_) == 0)
{
lean_object* v_us_1923_; lean_object* v_str_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; 
v_us_1923_ = lean_ctor_get(v_a_1920_, 1);
v_str_1924_ = lean_ctor_get(v_declName_1921_, 1);
v___x_1925_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType___closed__0));
v___x_1926_ = lean_string_dec_eq(v_str_1924_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__0));
v___x_1928_ = lean_string_dec_eq(v_str_1924_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__10));
v___x_1930_ = lean_string_dec_eq(v_str_1924_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1931_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__1));
v___x_1932_ = lean_string_dec_eq(v_str_1924_, v___x_1931_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__4));
v___x_1934_ = lean_string_dec_eq(v_str_1924_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1935_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__6));
v___x_1936_ = lean_string_dec_eq(v_str_1924_, v___x_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1937_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9));
v___x_1938_ = lean_string_dec_eq(v_str_1924_, v___x_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1939_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6));
v___x_1940_ = lean_string_dec_eq(v_str_1924_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3));
v___x_1942_ = lean_string_dec_eq(v_str_1924_, v___x_1941_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__0));
v___x_1944_ = lean_string_dec_eq(v_str_1924_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; uint8_t v___x_1946_; 
v___x_1945_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__3));
v___x_1946_ = lean_string_dec_eq(v_str_1924_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1947_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__2));
v___x_1948_ = lean_string_dec_eq(v_str_1924_, v___x_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; 
lean_dec(v_fst_1878_);
v___x_1949_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v_a_1920_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref_known(v_a_1920_, 2);
v___y_1890_ = v___x_1949_;
goto v___jp_1889_;
}
else
{
lean_inc(v_us_1923_);
lean_inc(v_pre_1922_);
lean_dec_ref_known(v_a_1920_, 2);
if (lean_obj_tag(v_us_1923_) == 0)
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; uint8_t v___x_1955_; uint8_t v___x_1956_; lean_object* v___x_1957_; 
lean_dec_ref(v___f_1911_);
lean_dec(v_snd_1883_);
v___x_1950_ = lean_unsigned_to_nat(8u);
v___x_1951_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__20));
v___x_1952_ = l_Lean_Expr_const___override(v___x_1951_, v_us_1923_);
v___x_1953_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1950_);
lean_ctor_set(v___x_1953_, 1, v___x_1884_);
lean_ctor_set(v___x_1953_, 2, v___x_1952_);
v___x_1954_ = lean_unbox(v_fst_1880_);
lean_dec(v_fst_1880_);
v___x_1955_ = lean_unbox(v_fst_1881_);
lean_dec(v_fst_1881_);
v___x_1956_ = lean_unbox(v_fst_1882_);
lean_dec(v_fst_1882_);
v___x_1957_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1878_, v___x_1953_, v_fst_1879_, v___x_1954_, v___x_1955_, v___x_1956_, v___x_1948_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
v___y_1890_ = v___x_1957_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
lean_dec(v_fst_1878_);
v___x_1958_ = l_Lean_Name_str___override(v_pre_1922_, v___x_1947_);
v___x_1959_ = l_Lean_Expr_const___override(v___x_1958_, v_us_1923_);
v___x_1960_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_1959_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___x_1959_);
v___y_1890_ = v___x_1960_;
goto v___jp_1889_;
}
}
}
else
{
lean_inc(v_us_1923_);
lean_inc(v_pre_1922_);
lean_dec_ref_known(v_a_1920_, 2);
if (lean_obj_tag(v_us_1923_) == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; uint8_t v___x_1966_; uint8_t v___x_1967_; lean_object* v___x_1968_; 
lean_dec_ref(v___f_1911_);
lean_dec(v_fst_1882_);
v___x_1961_ = lean_unsigned_to_nat(4u);
v___x_1962_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__17));
v___x_1963_ = l_Lean_Expr_const___override(v___x_1962_, v_us_1923_);
v___x_1964_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1961_);
lean_ctor_set(v___x_1964_, 1, v___x_1884_);
lean_ctor_set(v___x_1964_, 2, v___x_1963_);
v___x_1965_ = lean_unbox(v_fst_1880_);
lean_dec(v_fst_1880_);
v___x_1966_ = lean_unbox(v_fst_1881_);
lean_dec(v_fst_1881_);
v___x_1967_ = lean_unbox(v_snd_1883_);
lean_dec(v_snd_1883_);
v___x_1968_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1878_, v___x_1964_, v_fst_1879_, v___x_1965_, v___x_1966_, v___x_1946_, v___x_1967_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
v___y_1890_ = v___x_1968_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec(v_fst_1878_);
v___x_1969_ = l_Lean_Name_str___override(v_pre_1922_, v___x_1945_);
v___x_1970_ = l_Lean_Expr_const___override(v___x_1969_, v_us_1923_);
v___x_1971_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_1970_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___x_1970_);
v___y_1890_ = v___x_1971_;
goto v___jp_1889_;
}
}
}
else
{
lean_inc(v_us_1923_);
lean_inc(v_pre_1922_);
lean_dec_ref_known(v_a_1920_, 2);
if (lean_obj_tag(v_us_1923_) == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; uint8_t v___x_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; 
lean_dec_ref(v___f_1911_);
lean_dec(v_snd_1883_);
v___x_1972_ = lean_unsigned_to_nat(8u);
v___x_1973_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_builtinImpureType_x3f___closed__26));
v___x_1974_ = l_Lean_Expr_const___override(v___x_1973_, v_us_1923_);
v___x_1975_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1972_);
lean_ctor_set(v___x_1975_, 1, v___x_1884_);
lean_ctor_set(v___x_1975_, 2, v___x_1974_);
v___x_1976_ = lean_unbox(v_fst_1880_);
lean_dec(v_fst_1880_);
v___x_1977_ = lean_unbox(v_fst_1881_);
lean_dec(v_fst_1881_);
v___x_1978_ = lean_unbox(v_fst_1882_);
lean_dec(v_fst_1882_);
v___x_1979_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1878_, v___x_1975_, v_fst_1879_, v___x_1976_, v___x_1977_, v___x_1978_, v___x_1944_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
v___y_1890_ = v___x_1979_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
lean_dec(v_fst_1878_);
v___x_1980_ = l_Lean_Name_str___override(v_pre_1922_, v___x_1943_);
v___x_1981_ = l_Lean_Expr_const___override(v___x_1980_, v_us_1923_);
v___x_1982_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_1981_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___x_1981_);
v___y_1890_ = v___x_1982_;
goto v___jp_1889_;
}
}
}
else
{
lean_inc(v_us_1923_);
lean_inc(v_pre_1922_);
lean_dec_ref_known(v_a_1920_, 2);
if (lean_obj_tag(v_us_1923_) == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; uint8_t v___x_1988_; uint8_t v___x_1989_; lean_object* v___x_1990_; 
lean_dec_ref(v___f_1911_);
lean_dec(v_fst_1882_);
v___x_1983_ = lean_unsigned_to_nat(4u);
v___x_1984_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__4));
v___x_1985_ = l_Lean_Expr_const___override(v___x_1984_, v_us_1923_);
v___x_1986_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1983_);
lean_ctor_set(v___x_1986_, 1, v___x_1884_);
lean_ctor_set(v___x_1986_, 2, v___x_1985_);
v___x_1987_ = lean_unbox(v_fst_1880_);
lean_dec(v_fst_1880_);
v___x_1988_ = lean_unbox(v_fst_1881_);
lean_dec(v_fst_1881_);
v___x_1989_ = lean_unbox(v_snd_1883_);
lean_dec(v_snd_1883_);
v___x_1990_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1878_, v___x_1986_, v_fst_1879_, v___x_1987_, v___x_1988_, v___x_1942_, v___x_1989_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
v___y_1890_ = v___x_1990_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
lean_dec(v_fst_1878_);
v___x_1991_ = l_Lean_Name_str___override(v_pre_1922_, v___x_1941_);
v___x_1992_ = l_Lean_Expr_const___override(v___x_1991_, v_us_1923_);
v___x_1993_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_1992_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___x_1992_);
v___y_1890_ = v___x_1993_;
goto v___jp_1889_;
}
}
}
else
{
lean_inc(v_us_1923_);
lean_inc(v_pre_1922_);
lean_dec_ref_known(v_a_1920_, 2);
if (lean_obj_tag(v_us_1923_) == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; uint8_t v___x_1999_; uint8_t v___x_2000_; lean_object* v___x_2001_; 
lean_dec_ref(v___f_1911_);
lean_dec(v_fst_1881_);
v___x_1994_ = lean_unsigned_to_nat(2u);
v___x_1995_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__7));
v___x_1996_ = l_Lean_Expr_const___override(v___x_1995_, v_us_1923_);
v___x_1997_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1994_);
lean_ctor_set(v___x_1997_, 1, v___x_1884_);
lean_ctor_set(v___x_1997_, 2, v___x_1996_);
v___x_1998_ = lean_unbox(v_fst_1880_);
lean_dec(v_fst_1880_);
v___x_1999_ = lean_unbox(v_fst_1882_);
lean_dec(v_fst_1882_);
v___x_2000_ = lean_unbox(v_snd_1883_);
lean_dec(v_snd_1883_);
v___x_2001_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1878_, v___x_1997_, v_fst_1879_, v___x_1998_, v___x_1940_, v___x_1999_, v___x_2000_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
v___y_1890_ = v___x_2001_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
lean_dec(v_fst_1878_);
v___x_2002_ = l_Lean_Name_str___override(v_pre_1922_, v___x_1939_);
v___x_2003_ = l_Lean_Expr_const___override(v___x_2002_, v_us_1923_);
v___x_2004_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_2003_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___x_2003_);
v___y_1890_ = v___x_2004_;
goto v___jp_1889_;
}
}
}
else
{
lean_inc(v_us_1923_);
lean_inc(v_pre_1922_);
lean_dec_ref_known(v_a_1920_, 2);
if (lean_obj_tag(v_us_1923_) == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; uint8_t v___x_2009_; uint8_t v___x_2010_; lean_object* v___x_2011_; 
lean_dec_ref(v___f_1911_);
lean_dec(v_fst_1880_);
v___x_2005_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__10));
v___x_2006_ = l_Lean_Expr_const___override(v___x_2005_, v_us_1923_);
v___x_2007_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2007_, 0, v___x_1885_);
lean_ctor_set(v___x_2007_, 1, v___x_1884_);
lean_ctor_set(v___x_2007_, 2, v___x_2006_);
v___x_2008_ = lean_unbox(v_fst_1881_);
lean_dec(v_fst_1881_);
v___x_2009_ = lean_unbox(v_fst_1882_);
lean_dec(v_fst_1882_);
v___x_2010_ = lean_unbox(v_snd_1883_);
lean_dec(v_snd_1883_);
v___x_2011_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1878_, v___x_2007_, v_fst_1879_, v___x_1938_, v___x_2008_, v___x_2009_, v___x_2010_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
v___y_1890_ = v___x_2011_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec(v_fst_1878_);
v___x_2012_ = l_Lean_Name_str___override(v_pre_1922_, v___x_1937_);
v___x_2013_ = l_Lean_Expr_const___override(v___x_2012_, v_us_1923_);
v___x_2014_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_2013_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___x_2013_);
v___y_1890_ = v___x_2014_;
goto v___jp_1889_;
}
}
}
else
{
lean_inc(v_us_1923_);
lean_inc(v_pre_1922_);
lean_dec_ref_known(v_a_1920_, 2);
if (lean_obj_tag(v_us_1923_) == 0)
{
lean_object* v___x_2015_; uint8_t v___x_2016_; uint8_t v___x_2017_; uint8_t v___x_2018_; uint8_t v___x_2019_; lean_object* v___x_2020_; 
lean_dec_ref(v___f_1911_);
v___x_2015_ = lean_box(4);
v___x_2016_ = lean_unbox(v_fst_1880_);
lean_dec(v_fst_1880_);
v___x_2017_ = lean_unbox(v_fst_1881_);
lean_dec(v_fst_1881_);
v___x_2018_ = lean_unbox(v_fst_1882_);
lean_dec(v_fst_1882_);
v___x_2019_ = lean_unbox(v_snd_1883_);
lean_dec(v_snd_1883_);
v___x_2020_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1878_, v___x_2015_, v_fst_1879_, v___x_2016_, v___x_2017_, v___x_2018_, v___x_2019_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
v___y_1890_ = v___x_2020_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec(v_fst_1878_);
v___x_2021_ = l_Lean_Name_str___override(v_pre_1922_, v___x_1935_);
v___x_2022_ = l_Lean_Expr_const___override(v___x_2021_, v_us_1923_);
v___x_2023_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_2022_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___x_2022_);
v___y_1890_ = v___x_2023_;
goto v___jp_1889_;
}
}
}
else
{
lean_inc(v_us_1923_);
lean_inc(v_pre_1922_);
lean_dec_ref_known(v_a_1920_, 2);
if (lean_obj_tag(v_us_1923_) == 0)
{
lean_object* v___x_2024_; uint8_t v___x_2025_; uint8_t v___x_2026_; uint8_t v___x_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; 
lean_dec_ref(v___f_1911_);
v___x_2024_ = lean_box(0);
v___x_2025_ = lean_unbox(v_fst_1880_);
lean_dec(v_fst_1880_);
v___x_2026_ = lean_unbox(v_fst_1881_);
lean_dec(v_fst_1881_);
v___x_2027_ = lean_unbox(v_fst_1882_);
lean_dec(v_fst_1882_);
v___x_2028_ = lean_unbox(v_snd_1883_);
lean_dec(v_snd_1883_);
v___x_2029_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1878_, v___x_2024_, v_fst_1879_, v___x_2025_, v___x_2026_, v___x_2027_, v___x_2028_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
v___y_1890_ = v___x_2029_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_dec(v_fst_1878_);
v___x_2030_ = l_Lean_Name_str___override(v_pre_1922_, v___x_1933_);
v___x_2031_ = l_Lean_Expr_const___override(v___x_2030_, v_us_1923_);
v___x_2032_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_2031_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___x_2031_);
v___y_1890_ = v___x_2032_;
goto v___jp_1889_;
}
}
}
else
{
lean_inc(v_us_1923_);
lean_inc(v_pre_1922_);
lean_dec_ref_known(v_a_1920_, 2);
if (lean_obj_tag(v_us_1923_) == 0)
{
lean_object* v___x_2033_; uint8_t v___x_2034_; uint8_t v___x_2035_; uint8_t v___x_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; 
lean_dec_ref(v___f_1911_);
v___x_2033_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___closed__0));
v___x_2034_ = lean_unbox(v_fst_1880_);
lean_dec(v_fst_1880_);
v___x_2035_ = lean_unbox(v_fst_1881_);
lean_dec(v_fst_1881_);
v___x_2036_ = lean_unbox(v_fst_1882_);
lean_dec(v_fst_1882_);
v___x_2037_ = lean_unbox(v_snd_1883_);
lean_dec(v_snd_1883_);
v___x_2038_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_1878_, v___x_2033_, v_fst_1879_, v___x_2034_, v___x_2035_, v___x_2036_, v___x_2037_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
v___y_1890_ = v___x_2038_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
lean_dec(v_fst_1878_);
v___x_2039_ = l_Lean_Name_str___override(v_pre_1922_, v___x_1931_);
v___x_2040_ = l_Lean_Expr_const___override(v___x_2039_, v_us_1923_);
v___x_2041_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_2040_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___x_2040_);
v___y_1890_ = v___x_2041_;
goto v___jp_1889_;
}
}
}
else
{
lean_dec(v_fst_1878_);
if (lean_obj_tag(v_us_1923_) == 0)
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_box(0);
v___x_2043_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1879_, v___x_1885_, v_a_1920_, v___f_1911_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_2042_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
v___y_1890_ = v___x_2043_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
lean_inc(v_us_1923_);
lean_inc(v_pre_1922_);
lean_dec_ref_known(v_a_1920_, 2);
v___x_2044_ = l_Lean_Name_str___override(v_pre_1922_, v___x_1929_);
v___x_2045_ = l_Lean_Expr_const___override(v___x_2044_, v_us_1923_);
v___x_2046_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_2045_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___x_2045_);
v___y_1890_ = v___x_2046_;
goto v___jp_1889_;
}
}
}
else
{
lean_dec(v_fst_1878_);
if (lean_obj_tag(v_us_1923_) == 0)
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_box(0);
v___x_2048_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1879_, v___x_1885_, v_a_1920_, v___f_1911_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_2047_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
v___y_1890_ = v___x_2048_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_inc(v_us_1923_);
lean_inc(v_pre_1922_);
lean_dec_ref_known(v_a_1920_, 2);
v___x_2049_ = l_Lean_Name_str___override(v_pre_1922_, v___x_1927_);
v___x_2050_ = l_Lean_Expr_const___override(v___x_2049_, v_us_1923_);
v___x_2051_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_2050_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___x_2050_);
v___y_1890_ = v___x_2051_;
goto v___jp_1889_;
}
}
}
else
{
lean_dec(v_fst_1878_);
if (lean_obj_tag(v_us_1923_) == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = lean_box(0);
v___x_2053_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_1879_, v___x_1885_, v_a_1920_, v___f_1911_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_2052_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
v___y_1890_ = v___x_2053_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_inc(v_us_1923_);
lean_inc(v_pre_1922_);
lean_dec_ref_known(v_a_1920_, 2);
v___x_2054_ = l_Lean_Name_str___override(v_pre_1922_, v___x_1925_);
v___x_2055_ = l_Lean_Expr_const___override(v___x_2054_, v_us_1923_);
v___x_2056_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v___x_2055_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___x_2055_);
v___y_1890_ = v___x_2056_;
goto v___jp_1889_;
}
}
}
else
{
lean_object* v___x_2057_; 
lean_dec(v_fst_1878_);
v___x_2057_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v_a_1920_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref_known(v_a_1920_, 2);
v___y_1890_ = v___x_2057_;
goto v___jp_1889_;
}
}
else
{
lean_object* v___x_2058_; 
lean_dec(v_fst_1878_);
v___x_2058_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v_a_1920_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref_known(v_a_1920_, 2);
v___y_1890_ = v___x_2058_;
goto v___jp_1889_;
}
}
else
{
lean_object* v___x_2059_; 
lean_dec(v_fst_1878_);
v___x_2059_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_1911_, v_fst_1879_, v_fst_1880_, v_fst_1881_, v_fst_1882_, v_snd_1883_, v_a_1920_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v_a_1920_);
v___y_1890_ = v___x_2059_;
goto v___jp_1889_;
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec_ref(v___f_1911_);
lean_dec_ref(v___x_1888_);
lean_dec(v_snd_1883_);
lean_dec(v_fst_1882_);
lean_dec(v_fst_1881_);
lean_dec(v_fst_1880_);
lean_dec(v_fst_1879_);
lean_dec(v_fst_1878_);
v_a_2060_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_1919_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_1919_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec_ref(v___f_1911_);
lean_dec_ref(v___x_1888_);
lean_dec(v_snd_1883_);
lean_dec(v_fst_1882_);
lean_dec(v_fst_1881_);
lean_dec(v_fst_1880_);
lean_dec(v_fst_1879_);
lean_dec(v_fst_1878_);
v_a_2068_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_1917_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_1917_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec_ref(v___f_1911_);
lean_dec_ref(v___x_1888_);
lean_dec(v_snd_1883_);
lean_dec(v_fst_1882_);
lean_dec(v_fst_1881_);
lean_dec(v_fst_1880_);
lean_dec(v_fst_1879_);
lean_dec(v_fst_1878_);
v_a_2076_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_1915_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_1915_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec_ref(v___f_1911_);
lean_dec_ref(v___x_1888_);
lean_dec(v_snd_1883_);
lean_dec(v_fst_1882_);
lean_dec(v_fst_1881_);
lean_dec(v_fst_1880_);
lean_dec(v_fst_1879_);
lean_dec(v_fst_1878_);
v_a_2084_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_1913_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_1913_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
v___jp_1889_:
{
if (lean_obj_tag(v___y_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1901_; 
v_a_1891_ = lean_ctor_get(v___y_1890_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___y_1890_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1893_ = v___y_1890_;
v_isShared_1894_ = v_isSharedCheck_1901_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___y_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1901_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
if (lean_obj_tag(v_a_1891_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; 
lean_dec_ref(v___x_1888_);
v_a_1895_ = lean_ctor_get(v_a_1891_, 0);
lean_inc(v_a_1895_);
lean_dec_ref_known(v_a_1891_, 1);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v_a_1895_);
v___x_1897_ = v___x_1893_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
else
{
lean_object* v_a_1899_; 
lean_del_object(v___x_1893_);
v_a_1899_ = lean_ctor_get(v_a_1891_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v_a_1891_, 1);
v_a_1859_ = v___x_1888_;
v_b_1860_ = v_a_1899_;
goto _start;
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec_ref(v___x_1888_);
v_a_1902_ = lean_ctor_get(v___y_1890_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___y_1890_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___y_1890_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___y_1890_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___boxed(lean_object* v_a_2094_, lean_object* v_b_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v_a_2094_, v_b_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1(lean_object* v_numFields_2102_, lean_object* v_numParams_2103_, uint8_t v___x_2104_, lean_object* v_ctorName_2105_, lean_object* v_cidx_2106_, lean_object* v___f_2107_, lean_object* v_params_2108_, lean_object* v_x_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2115_ = lean_mk_empty_array_with_capacity(v_numFields_2102_);
v___x_2116_ = lean_unsigned_to_nat(0u);
v___x_2117_ = lean_nat_add(v_numParams_2103_, v_numFields_2102_);
v___x_2118_ = l_Array_toSubarray___redArg(v_params_2108_, v_numParams_2103_, v___x_2117_);
v___x_2119_ = lean_box(v___x_2104_);
v___x_2120_ = lean_box(v___x_2104_);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = lean_box(v___x_2104_);
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v___x_2121_);
v___x_2124_ = lean_box(v___x_2104_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
lean_ctor_set(v___x_2125_, 1, v___x_2123_);
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2116_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2115_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v___x_2118_, v___x_2127_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2192_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2192_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2128_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2192_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v_snd_2133_; lean_object* v_fst_2134_; lean_object* v_fst_2135_; lean_object* v_snd_2136_; size_t v_sz_2137_; size_t v___x_2138_; lean_object* v___x_2139_; lean_object* v_snd_2140_; lean_object* v_snd_2141_; lean_object* v_fst_2142_; lean_object* v_snd_2143_; lean_object* v_fst_2144_; lean_object* v_fst_2145_; lean_object* v_fst_2146_; lean_object* v_snd_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2191_; 
v_snd_2133_ = lean_ctor_get(v_a_2129_, 1);
lean_inc(v_snd_2133_);
v_fst_2134_ = lean_ctor_get(v_a_2129_, 0);
lean_inc(v_fst_2134_);
lean_dec(v_a_2129_);
v_fst_2135_ = lean_ctor_get(v_snd_2133_, 0);
lean_inc_n(v_fst_2135_, 2);
v_snd_2136_ = lean_ctor_get(v_snd_2133_, 1);
lean_inc(v_snd_2136_);
lean_dec(v_snd_2133_);
v_sz_2137_ = lean_array_size(v_fst_2134_);
v___x_2138_ = ((size_t)0ULL);
v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__4(v_sz_2137_, v___x_2138_, v_fst_2134_, v_fst_2135_);
v_snd_2140_ = lean_ctor_get(v_snd_2136_, 1);
lean_inc(v_snd_2140_);
v_snd_2141_ = lean_ctor_get(v_snd_2140_, 1);
lean_inc(v_snd_2141_);
v_fst_2142_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_fst_2142_);
v_snd_2143_ = lean_ctor_get(v___x_2139_, 1);
lean_inc(v_snd_2143_);
lean_dec_ref(v___x_2139_);
v_fst_2144_ = lean_ctor_get(v_snd_2136_, 0);
lean_inc(v_fst_2144_);
lean_dec(v_snd_2136_);
v_fst_2145_ = lean_ctor_get(v_snd_2140_, 0);
lean_inc(v_fst_2145_);
lean_dec(v_snd_2140_);
v_fst_2146_ = lean_ctor_get(v_snd_2141_, 0);
v_snd_2147_ = lean_ctor_get(v_snd_2141_, 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_snd_2141_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2149_ = v_snd_2141_;
v_isShared_2150_ = v_isSharedCheck_2191_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_snd_2147_);
lean_inc(v_fst_2146_);
lean_dec(v_snd_2141_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2191_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2151_; lean_object* v_fields_2153_; lean_object* v_nextOffset_2154_; lean_object* v_fields_2163_; lean_object* v_nextOffset_2164_; lean_object* v_fields_2171_; lean_object* v_nextOffset_2172_; lean_object* v_fields_2179_; lean_object* v_nextOffset_2180_; uint8_t v___x_2186_; 
v___x_2151_ = lean_nat_sub(v_snd_2143_, v_fst_2135_);
lean_dec(v_snd_2143_);
v___x_2186_ = lean_unbox(v_snd_2147_);
lean_dec(v_snd_2147_);
if (v___x_2186_ == 0)
{
v_fields_2179_ = v_fst_2142_;
v_nextOffset_2180_ = v___x_2116_;
goto v___jp_2178_;
}
else
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v_fst_2189_; lean_object* v_snd_2190_; 
v___x_2187_ = lean_unsigned_to_nat(8u);
lean_inc_ref(v___f_2107_);
v___x_2188_ = lean_apply_3(v___f_2107_, v_fst_2142_, v___x_2187_, v___x_2116_);
v_fst_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_fst_2189_);
v_snd_2190_ = lean_ctor_get(v___x_2188_, 1);
lean_inc(v_snd_2190_);
lean_dec_ref(v___x_2188_);
v_fields_2179_ = v_fst_2189_;
v_nextOffset_2180_ = v_snd_2190_;
goto v___jp_2178_;
}
v___jp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2155_, 0, v_ctorName_2105_);
lean_ctor_set(v___x_2155_, 1, v_cidx_2106_);
lean_ctor_set(v___x_2155_, 2, v_fst_2135_);
lean_ctor_set(v___x_2155_, 3, v___x_2151_);
lean_ctor_set(v___x_2155_, 4, v_nextOffset_2154_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 1, v_fields_2153_);
lean_ctor_set(v___x_2149_, 0, v___x_2155_);
v___x_2157_ = v___x_2149_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2155_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_fields_2153_);
v___x_2157_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2159_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2157_);
v___x_2159_ = v___x_2131_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
v___jp_2162_:
{
uint8_t v___x_2165_; 
v___x_2165_ = lean_unbox(v_fst_2144_);
lean_dec(v_fst_2144_);
if (v___x_2165_ == 0)
{
lean_dec_ref(v___f_2107_);
v_fields_2153_ = v_fields_2163_;
v_nextOffset_2154_ = v_nextOffset_2164_;
goto v___jp_2152_;
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v_fst_2168_; lean_object* v_snd_2169_; 
v___x_2166_ = lean_unsigned_to_nat(1u);
v___x_2167_ = lean_apply_3(v___f_2107_, v_fields_2163_, v___x_2166_, v_nextOffset_2164_);
v_fst_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_fst_2168_);
v_snd_2169_ = lean_ctor_get(v___x_2167_, 1);
lean_inc(v_snd_2169_);
lean_dec_ref(v___x_2167_);
v_fields_2153_ = v_fst_2168_;
v_nextOffset_2154_ = v_snd_2169_;
goto v___jp_2152_;
}
}
v___jp_2170_:
{
uint8_t v___x_2173_; 
v___x_2173_ = lean_unbox(v_fst_2145_);
lean_dec(v_fst_2145_);
if (v___x_2173_ == 0)
{
v_fields_2163_ = v_fields_2171_;
v_nextOffset_2164_ = v_nextOffset_2172_;
goto v___jp_2162_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v_fst_2176_; lean_object* v_snd_2177_; 
v___x_2174_ = lean_unsigned_to_nat(2u);
lean_inc_ref(v___f_2107_);
v___x_2175_ = lean_apply_3(v___f_2107_, v_fields_2171_, v___x_2174_, v_nextOffset_2172_);
v_fst_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_fst_2176_);
v_snd_2177_ = lean_ctor_get(v___x_2175_, 1);
lean_inc(v_snd_2177_);
lean_dec_ref(v___x_2175_);
v_fields_2163_ = v_fst_2176_;
v_nextOffset_2164_ = v_snd_2177_;
goto v___jp_2162_;
}
}
v___jp_2178_:
{
uint8_t v___x_2181_; 
v___x_2181_ = lean_unbox(v_fst_2146_);
lean_dec(v_fst_2146_);
if (v___x_2181_ == 0)
{
v_fields_2171_ = v_fields_2179_;
v_nextOffset_2172_ = v_nextOffset_2180_;
goto v___jp_2170_;
}
else
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v_fst_2184_; lean_object* v_snd_2185_; 
v___x_2182_ = lean_unsigned_to_nat(4u);
lean_inc_ref(v___f_2107_);
v___x_2183_ = lean_apply_3(v___f_2107_, v_fields_2179_, v___x_2182_, v_nextOffset_2180_);
v_fst_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_fst_2184_);
v_snd_2185_ = lean_ctor_get(v___x_2183_, 1);
lean_inc(v_snd_2185_);
lean_dec_ref(v___x_2183_);
v_fields_2171_ = v_fst_2184_;
v_nextOffset_2172_ = v_snd_2185_;
goto v___jp_2170_;
}
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec_ref(v___f_2107_);
lean_dec(v_cidx_2106_);
lean_dec(v_ctorName_2105_);
v_a_2193_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2128_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2128_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___boxed(lean_object* v_numFields_2201_, lean_object* v_numParams_2202_, lean_object* v___x_2203_, lean_object* v_ctorName_2204_, lean_object* v_cidx_2205_, lean_object* v___f_2206_, lean_object* v_params_2207_, lean_object* v_x_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
uint8_t v___x_13798__boxed_2214_; lean_object* v_res_2215_; 
v___x_13798__boxed_2214_ = lean_unbox(v___x_2203_);
v_res_2215_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1(v_numFields_2201_, v_numParams_2202_, v___x_13798__boxed_2214_, v_ctorName_2204_, v_cidx_2205_, v___f_2206_, v_params_2207_, v_x_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec_ref(v_x_2208_);
lean_dec(v_numFields_2201_);
return v_res_2215_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2216_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_2217_ = lean_unsigned_to_nat(66u);
v___x_2218_ = lean_unsigned_to_nat(199u);
v___x_2219_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0));
v___x_2220_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_2221_ = l_mkPanicMessageWithDecl(v___x_2220_, v___x_2219_, v___x_2218_, v___x_2217_, v___x_2216_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(lean_object* v_ctorName_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___f_2232_; lean_object* v___x_2233_; lean_object* v_env_2234_; uint8_t v___x_2235_; lean_object* v___x_2236_; 
v___f_2232_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__1));
v___x_2233_ = lean_st_ref_get(v_a_2225_);
v_env_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc_ref(v_env_2234_);
lean_dec(v___x_2233_);
v___x_2235_ = 0;
lean_inc(v_ctorName_2223_);
v___x_2236_ = l_Lean_Environment_find_x3f(v_env_2234_, v_ctorName_2223_, v___x_2235_);
if (lean_obj_tag(v___x_2236_) == 1)
{
lean_object* v_val_2237_; 
v_val_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_val_2237_);
lean_dec_ref_known(v___x_2236_, 1);
if (lean_obj_tag(v_val_2237_) == 6)
{
lean_object* v_val_2238_; lean_object* v_toConstantVal_2239_; lean_object* v_cidx_2240_; lean_object* v_numParams_2241_; lean_object* v_numFields_2242_; lean_object* v_type_2243_; lean_object* v___x_2244_; lean_object* v___f_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v_val_2238_ = lean_ctor_get(v_val_2237_, 0);
lean_inc_ref(v_val_2238_);
lean_dec_ref_known(v_val_2237_, 1);
v_toConstantVal_2239_ = lean_ctor_get(v_val_2238_, 0);
lean_inc_ref(v_toConstantVal_2239_);
v_cidx_2240_ = lean_ctor_get(v_val_2238_, 2);
lean_inc(v_cidx_2240_);
v_numParams_2241_ = lean_ctor_get(v_val_2238_, 3);
lean_inc(v_numParams_2241_);
v_numFields_2242_ = lean_ctor_get(v_val_2238_, 4);
lean_inc(v_numFields_2242_);
lean_dec_ref(v_val_2238_);
v_type_2243_ = lean_ctor_get(v_toConstantVal_2239_, 2);
lean_inc_ref(v_type_2243_);
lean_dec_ref(v_toConstantVal_2239_);
v___x_2244_ = lean_box(v___x_2235_);
v___f_2245_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___lam__1___boxed), 13, 6);
lean_closure_set(v___f_2245_, 0, v_numFields_2242_);
lean_closure_set(v___f_2245_, 1, v_numParams_2241_);
lean_closure_set(v___f_2245_, 2, v___x_2244_);
lean_closure_set(v___f_2245_, 3, v_ctorName_2223_);
lean_closure_set(v___f_2245_, 4, v_cidx_2240_);
lean_closure_set(v___f_2245_, 5, v___f_2232_);
v___x_2246_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__13);
v___x_2247_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__17);
v___x_2248_ = lean_st_mk_ref(v___x_2247_);
v___x_2249_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__5___redArg(v_type_2243_, v___f_2245_, v___x_2235_, v___x_2235_, v___x_2246_, v___x_2248_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2258_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2258_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2258_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2254_ = lean_st_ref_get(v___x_2248_);
lean_dec(v___x_2248_);
lean_dec(v___x_2254_);
if (v_isShared_2253_ == 0)
{
v___x_2256_ = v___x_2252_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2250_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
else
{
lean_dec(v___x_2248_);
return v___x_2249_;
}
}
else
{
lean_dec(v_val_2237_);
lean_dec(v_ctorName_2223_);
v___y_2228_ = v_a_2224_;
v___y_2229_ = v_a_2225_;
goto v___jp_2227_;
}
}
else
{
lean_dec(v___x_2236_);
lean_dec(v_ctorName_2223_);
v___y_2228_ = v_a_2224_;
v___y_2229_ = v_a_2225_;
goto v___jp_2227_;
}
v___jp_2227_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0, &l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___closed__0);
v___x_2231_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__1(v___x_2230_, v___y_2228_, v___y_2229_);
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache___boxed(lean_object* v_ctorName_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(v_ctorName_2259_, v_a_2260_, v_a_2261_);
lean_dec(v_a_2261_);
lean_dec_ref(v_a_2260_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3(lean_object* v_inst_2264_, lean_object* v_R_2265_, lean_object* v_a_2266_, lean_object* v_b_2267_, lean_object* v_c_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___redArg(v_a_2266_, v_b_2267_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3___boxed(lean_object* v_inst_2275_, lean_object* v_R_2276_, lean_object* v_a_2277_, lean_object* v_b_2278_, lean_object* v_c_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache_spec__3(v_inst_2275_, v_R_2276_, v_a_2277_, v_b_2278_, v_c_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setCtorLayout(lean_object* v_ctorName_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v_env_2292_; lean_object* v___x_2293_; lean_object* v_toEnvExtension_2294_; lean_object* v_asyncMode_2295_; uint8_t v___x_2296_; lean_object* v___x_2297_; 
v___x_2290_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
v___x_2291_ = lean_st_ref_get(v_a_2288_);
v_env_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc_ref(v_env_2292_);
lean_dec(v___x_2291_);
v___x_2293_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt;
v_toEnvExtension_2294_ = lean_ctor_get(v___x_2293_, 0);
v_asyncMode_2295_ = lean_ctor_get(v_toEnvExtension_2294_, 2);
v___x_2296_ = 0;
lean_inc(v_ctorName_2286_);
v___x_2297_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2290_, v___x_2293_, v_env_2292_, v_ctorName_2286_, v_asyncMode_2295_, v___x_2296_);
if (lean_obj_tag(v___x_2297_) == 0)
{
uint8_t v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = 0;
lean_inc(v_ctorName_2286_);
v___x_2299_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_fillCache(v_ctorName_2286_, v_a_2287_, v_a_2288_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc_n(v_a_2300_, 2);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_setCtorLayout_checkCtorLayout(v_a_2300_, v_a_2287_, v_a_2288_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2330_; 
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2330_ == 0)
{
lean_object* v_unused_2331_; 
v_unused_2331_ = lean_ctor_get(v___x_2301_, 0);
lean_dec(v_unused_2331_);
v___x_2303_ = v___x_2301_;
v_isShared_2304_ = v_isSharedCheck_2330_;
goto v_resetjp_2302_;
}
else
{
lean_dec(v___x_2301_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2330_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; lean_object* v_env_2306_; lean_object* v_nextMacroScope_2307_; lean_object* v_ngen_2308_; lean_object* v_auxDeclNGen_2309_; lean_object* v_traceState_2310_; lean_object* v_recordedDeps_2311_; lean_object* v_messages_2312_; lean_object* v_infoState_2313_; lean_object* v_snapshotTasks_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2328_; 
v___x_2305_ = lean_st_ref_take(v_a_2288_);
v_env_2306_ = lean_ctor_get(v___x_2305_, 0);
v_nextMacroScope_2307_ = lean_ctor_get(v___x_2305_, 1);
v_ngen_2308_ = lean_ctor_get(v___x_2305_, 2);
v_auxDeclNGen_2309_ = lean_ctor_get(v___x_2305_, 3);
v_traceState_2310_ = lean_ctor_get(v___x_2305_, 4);
v_recordedDeps_2311_ = lean_ctor_get(v___x_2305_, 6);
v_messages_2312_ = lean_ctor_get(v___x_2305_, 7);
v_infoState_2313_ = lean_ctor_get(v___x_2305_, 8);
v_snapshotTasks_2314_ = lean_ctor_get(v___x_2305_, 9);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2328_ == 0)
{
lean_object* v_unused_2329_; 
v_unused_2329_ = lean_ctor_get(v___x_2305_, 5);
lean_dec(v_unused_2329_);
v___x_2316_ = v___x_2305_;
v_isShared_2317_ = v_isSharedCheck_2328_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_snapshotTasks_2314_);
lean_inc(v_infoState_2313_);
lean_inc(v_messages_2312_);
lean_inc(v_recordedDeps_2311_);
lean_inc(v_traceState_2310_);
lean_inc(v_auxDeclNGen_2309_);
lean_inc(v_ngen_2308_);
lean_inc(v_nextMacroScope_2307_);
lean_inc(v_env_2306_);
lean_dec(v___x_2305_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2328_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2322_; 
v___x_2318_ = lean_box(0);
v___x_2319_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2293_, v_env_2306_, v_ctorName_2286_, v_a_2300_, v___x_2298_);
v___x_2320_ = lean_obj_once(&l_Lean_Compiler_LCNF_setImpureType___closed__1, &l_Lean_Compiler_LCNF_setImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_setImpureType___closed__1);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 5, v___x_2320_);
lean_ctor_set(v___x_2316_, 0, v___x_2319_);
v___x_2322_ = v___x_2316_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2319_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_nextMacroScope_2307_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_ngen_2308_);
lean_ctor_set(v_reuseFailAlloc_2327_, 3, v_auxDeclNGen_2309_);
lean_ctor_set(v_reuseFailAlloc_2327_, 4, v_traceState_2310_);
lean_ctor_set(v_reuseFailAlloc_2327_, 5, v___x_2320_);
lean_ctor_set(v_reuseFailAlloc_2327_, 6, v_recordedDeps_2311_);
lean_ctor_set(v_reuseFailAlloc_2327_, 7, v_messages_2312_);
lean_ctor_set(v_reuseFailAlloc_2327_, 8, v_infoState_2313_);
lean_ctor_set(v_reuseFailAlloc_2327_, 9, v_snapshotTasks_2314_);
v___x_2322_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2323_ = lean_st_ref_put(v_a_2288_, v___x_2322_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2318_);
v___x_2325_ = v___x_2303_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2318_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
else
{
lean_dec(v_a_2300_);
lean_dec(v_ctorName_2286_);
return v___x_2301_;
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v_ctorName_2286_);
v_a_2332_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2299_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2299_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v_ctorName_2286_);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v___x_2297_, 0);
lean_dec(v_unused_2348_);
v___x_2341_ = v___x_2297_;
v_isShared_2342_ = v_isSharedCheck_2347_;
goto v_resetjp_2340_;
}
else
{
lean_dec(v___x_2297_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2347_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2343_ = lean_box(0);
if (v_isShared_2342_ == 0)
{
lean_ctor_set_tag(v___x_2341_, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2343_);
v___x_2345_ = v___x_2341_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setCtorLayout___boxed(lean_object* v_ctorName_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_Compiler_LCNF_setCtorLayout(v_ctorName_2349_, v_a_2350_, v_a_2351_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getCtorLayout(lean_object* v_ctorName_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v_env_2360_; lean_object* v___x_2361_; lean_object* v_toEnvExtension_2362_; lean_object* v_asyncMode_2363_; uint8_t v___x_2364_; lean_object* v___x_2365_; 
v___x_2358_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
v___x_2359_ = lean_st_ref_get(v_a_2356_);
v_env_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc_ref(v_env_2360_);
lean_dec(v___x_2359_);
v___x_2361_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt;
v_toEnvExtension_2362_ = lean_ctor_get(v___x_2361_, 0);
v_asyncMode_2363_ = lean_ctor_get(v_toEnvExtension_2362_, 2);
v___x_2364_ = 0;
lean_inc(v_ctorName_2354_);
v___x_2365_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2358_, v___x_2361_, v_env_2360_, v_ctorName_2354_, v_asyncMode_2363_, v___x_2364_);
if (lean_obj_tag(v___x_2365_) == 1)
{
lean_object* v_val_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_ctorName_2354_);
v_val_2366_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2365_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_val_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
lean_ctor_set_tag(v___x_2368_, 0);
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_val_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
lean_dec(v___x_2365_);
v___x_2374_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__1, &l_Lean_Compiler_LCNF_nameToImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1);
v___x_2375_ = l_Lean_MessageData_ofName(v_ctorName_2354_);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__3, &l_Lean_Compiler_LCNF_nameToImpureType___closed__3_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__3);
v___x_2378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2376_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v___x_2378_, v_a_2355_, v_a_2356_);
return v___x_2379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getCtorLayout___boxed(lean_object* v_ctorName_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(lean_object* v_as_2385_, size_t v_sz_2386_, size_t v_i_2387_, lean_object* v_b_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
uint8_t v___x_2392_; 
v___x_2392_ = lean_usize_dec_lt(v_i_2387_, v_sz_2386_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; 
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v_b_2388_);
return v___x_2393_;
}
else
{
lean_object* v___x_2394_; lean_object* v_a_2395_; lean_object* v___x_2396_; 
v___x_2394_ = lean_box(0);
v_a_2395_ = lean_array_uget_borrowed(v_as_2385_, v_i_2387_);
lean_inc(v_a_2395_);
v___x_2396_ = l_Lean_Compiler_LCNF_setHasTrivialStructure_x3f(v_a_2395_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v___x_2397_; 
lean_dec_ref_known(v___x_2396_, 1);
lean_inc(v_a_2395_);
v___x_2397_ = l_Lean_Compiler_LCNF_setHasTrivialImpureStructure_x3f(v_a_2395_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2397_) == 0)
{
size_t v___x_2398_; size_t v___x_2399_; 
lean_dec_ref_known(v___x_2397_, 1);
v___x_2398_ = ((size_t)1ULL);
v___x_2399_ = lean_usize_add(v_i_2387_, v___x_2398_);
v_i_2387_ = v___x_2399_;
v_b_2388_ = v___x_2394_;
goto _start;
}
else
{
return v___x_2397_;
}
}
else
{
return v___x_2396_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2___boxed(lean_object* v_as_2401_, lean_object* v_sz_2402_, lean_object* v_i_2403_, lean_object* v_b_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
size_t v_sz_boxed_2408_; size_t v_i_boxed_2409_; lean_object* v_res_2410_; 
v_sz_boxed_2408_ = lean_unbox_usize(v_sz_2402_);
lean_dec(v_sz_2402_);
v_i_boxed_2409_ = lean_unbox_usize(v_i_2403_);
lean_dec(v_i_2403_);
v_res_2410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(v_as_2401_, v_sz_boxed_2408_, v_i_boxed_2409_, v_b_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec_ref(v_as_2401_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(lean_object* v_as_x27_2411_, lean_object* v_b_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
if (lean_obj_tag(v_as_x27_2411_) == 0)
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2416_, 0, v_b_2412_);
return v___x_2416_;
}
else
{
lean_object* v_head_2417_; lean_object* v_tail_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_head_2417_ = lean_ctor_get(v_as_x27_2411_, 0);
v_tail_2418_ = lean_ctor_get(v_as_x27_2411_, 1);
v___x_2419_ = lean_box(0);
lean_inc(v_head_2417_);
v___x_2420_ = l_Lean_Compiler_LCNF_setOtherDeclMonoType(v_head_2417_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v___x_2421_; 
lean_dec_ref_known(v___x_2420_, 1);
lean_inc(v_head_2417_);
v___x_2421_ = l_Lean_Compiler_LCNF_setCtorLayout(v_head_2417_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_dec_ref_known(v___x_2421_, 1);
v_as_x27_2411_ = v_tail_2418_;
v_b_2412_ = v___x_2419_;
goto _start;
}
else
{
return v___x_2421_;
}
}
else
{
return v___x_2420_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg___boxed(lean_object* v_as_x27_2423_, lean_object* v_b_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(v_as_x27_2423_, v_b_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v_as_x27_2423_);
return v_res_2428_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_2431_ = l_Lean_stringToMessageData(v___x_2430_);
return v___x_2431_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_2434_ = l_Lean_stringToMessageData(v___x_2433_);
return v___x_2434_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_2437_ = l_Lean_stringToMessageData(v___x_2436_);
return v___x_2437_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_2440_ = l_Lean_stringToMessageData(v___x_2439_);
return v___x_2440_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_2443_ = l_Lean_stringToMessageData(v___x_2442_);
return v___x_2443_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_2446_ = l_Lean_stringToMessageData(v___x_2445_);
return v___x_2446_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_2449_ = l_Lean_stringToMessageData(v___x_2448_);
return v___x_2449_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_2452_ = l_Lean_stringToMessageData(v___x_2451_);
return v___x_2452_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_2458_ = l_Lean_stringToMessageData(v___x_2457_);
return v___x_2458_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__21(void){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__20));
v___x_2461_ = l_Lean_stringToMessageData(v___x_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2462_, lean_object* v_declHint_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v_env_2468_; uint8_t v___x_2469_; 
v___x_2466_ = lean_box(0);
v___x_2467_ = lean_st_ref_get(v___y_2464_);
v_env_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc_ref(v_env_2468_);
lean_dec(v___x_2467_);
v___x_2469_ = l_Lean_Name_isAnonymous(v_declHint_2463_);
if (v___x_2469_ == 0)
{
uint8_t v_isExporting_2470_; 
v_isExporting_2470_ = lean_ctor_get_uint8(v_env_2468_, sizeof(void*)*13);
if (v_isExporting_2470_ == 0)
{
lean_object* v___x_2471_; 
lean_dec_ref(v_env_2468_);
lean_dec(v_declHint_2463_);
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v_msg_2462_);
return v___x_2471_;
}
else
{
lean_object* v___x_2472_; uint8_t v___x_2473_; 
lean_inc_ref(v_env_2468_);
v___x_2472_ = l_Lean_Environment_setExporting(v_env_2468_, v___x_2469_);
lean_inc(v_declHint_2463_);
lean_inc_ref(v___x_2472_);
v___x_2473_ = l_Lean_Environment_contains(v___x_2472_, v_declHint_2463_, v_isExporting_2470_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; 
lean_dec_ref(v___x_2472_);
lean_dec_ref(v_env_2468_);
lean_dec(v_declHint_2463_);
v___x_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2474_, 0, v_msg_2462_);
return v___x_2474_;
}
else
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v_c_2480_; lean_object* v___x_2481_; 
v___x_2475_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__1);
v___x_2476_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0_spec__0___closed__2);
v___x_2477_ = l_Lean_Options_empty;
v___x_2478_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2472_);
lean_ctor_set(v___x_2478_, 1, v___x_2475_);
lean_ctor_set(v___x_2478_, 2, v___x_2476_);
lean_ctor_set(v___x_2478_, 3, v___x_2477_);
lean_inc(v_declHint_2463_);
v___x_2479_ = l_Lean_MessageData_ofConstName(v_declHint_2463_, v___x_2469_);
v_c_2480_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2480_, 0, v___x_2478_);
lean_ctor_set(v_c_2480_, 1, v___x_2479_);
v___x_2481_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2468_, v_declHint_2463_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
lean_dec_ref(v_env_2468_);
lean_dec(v_declHint_2463_);
v___x_2482_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
lean_ctor_set(v___x_2483_, 1, v_c_2480_);
v___x_2484_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_2485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = l_Lean_MessageData_note(v___x_2485_);
v___x_2487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2487_, 0, v_msg_2462_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
return v___x_2488_;
}
else
{
lean_object* v_val_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2545_; 
v_val_2489_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2491_ = v___x_2481_;
v_isShared_2492_ = v_isSharedCheck_2545_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_val_2489_);
lean_dec(v___x_2481_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2545_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v_modules_2494_; lean_object* v_moduleNames_2495_; lean_object* v_mod_2496_; uint8_t v___y_2498_; uint8_t v___x_2528_; 
v___x_2493_ = l_Lean_Environment_header(v_env_2468_);
lean_dec_ref(v_env_2468_);
v_modules_2494_ = lean_ctor_get(v___x_2493_, 3);
lean_inc_ref(v_modules_2494_);
v_moduleNames_2495_ = lean_ctor_get(v___x_2493_, 4);
lean_inc_ref(v_moduleNames_2495_);
lean_dec_ref(v___x_2493_);
v_mod_2496_ = lean_array_get(v___x_2466_, v_moduleNames_2495_, v_val_2489_);
lean_dec_ref(v_moduleNames_2495_);
v___x_2528_ = l_Lean_isPrivateName(v_declHint_2463_);
lean_dec(v_declHint_2463_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2529_ = lean_array_get_size(v_modules_2494_);
v___x_2530_ = lean_nat_dec_lt(v_val_2489_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_dec_ref(v_modules_2494_);
lean_dec(v_val_2489_);
v___y_2498_ = v___x_2528_;
goto v___jp_2497_;
}
else
{
lean_object* v___x_2531_; lean_object* v_toImport_2532_; uint8_t v_isExported_2533_; 
v___x_2531_ = lean_array_fget(v_modules_2494_, v_val_2489_);
lean_dec(v_val_2489_);
lean_dec_ref(v_modules_2494_);
v_toImport_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc_ref(v_toImport_2532_);
lean_dec(v___x_2531_);
v_isExported_2533_ = lean_ctor_get_uint8(v_toImport_2532_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2532_);
v___y_2498_ = v_isExported_2533_;
goto v___jp_2497_;
}
}
else
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_dec_ref(v_modules_2494_);
lean_del_object(v___x_2491_);
lean_dec(v_val_2489_);
v___x_2534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
lean_ctor_set(v___x_2535_, 1, v_c_2480_);
v___x_2536_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_2537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = l_Lean_MessageData_ofName(v_mod_2496_);
v___x_2539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__21);
v___x_2541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2539_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
v___x_2542_ = l_Lean_MessageData_note(v___x_2541_);
v___x_2543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2543_, 0, v_msg_2462_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
return v___x_2544_;
}
v___jp_2497_:
{
if (v___y_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2499_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_2500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
lean_ctor_set(v___x_2500_, 1, v_c_2480_);
v___x_2501_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_2502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2500_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = l_Lean_MessageData_ofName(v_mod_2496_);
v___x_2504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2502_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_2506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2504_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = l_Lean_MessageData_note(v___x_2506_);
v___x_2508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2508_, 0, v_msg_2462_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set_tag(v___x_2491_, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2508_);
v___x_2510_ = v___x_2491_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2526_; 
v___x_2512_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_2513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
lean_ctor_set(v___x_2513_, 1, v_c_2480_);
v___x_2514_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_2515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v___x_2516_ = l_Lean_MessageData_ofName(v_mod_2496_);
lean_inc_ref(v___x_2516_);
v___x_2517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_2519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
lean_ctor_set(v___x_2520_, 1, v___x_2516_);
v___x_2521_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = l_Lean_MessageData_note(v___x_2522_);
v___x_2524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2524_, 0, v_msg_2462_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set_tag(v___x_2491_, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2524_);
v___x_2526_ = v___x_2491_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
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
lean_object* v___x_2546_; 
lean_dec_ref(v_env_2468_);
lean_dec(v_declHint_2463_);
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v_msg_2462_);
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2547_, lean_object* v_declHint_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_2547_, v_declHint_2548_, v___y_2549_);
lean_dec(v___y_2549_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(lean_object* v_msg_2552_, lean_object* v_declHint_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v___x_2557_; lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2567_; 
v___x_2557_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_2552_, v_declHint_2553_, v___y_2555_);
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2567_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2567_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2565_; 
v___x_2562_ = l_Lean_unknownIdentifierMessageTag;
v___x_2563_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
lean_ctor_set(v___x_2563_, 1, v_a_2558_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v___x_2563_);
v___x_2565_ = v___x_2560_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8___boxed(lean_object* v_msg_2568_, lean_object* v_declHint_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_2568_, v_declHint_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(lean_object* v_ref_2574_, lean_object* v_msg_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_toCold_2579_; lean_object* v_currRecDepth_2580_; lean_object* v_ref_2581_; uint16_t v_optionFlags_2582_; uint8_t v_suppressElabErrors_2583_; uint8_t v_isRecordingDeps_2584_; lean_object* v_ref_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v_toCold_2579_ = lean_ctor_get(v___y_2576_, 0);
v_currRecDepth_2580_ = lean_ctor_get(v___y_2576_, 1);
v_ref_2581_ = lean_ctor_get(v___y_2576_, 2);
v_optionFlags_2582_ = lean_ctor_get_uint16(v___y_2576_, sizeof(void*)*3);
v_suppressElabErrors_2583_ = lean_ctor_get_uint8(v___y_2576_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2584_ = lean_ctor_get_uint8(v___y_2576_, sizeof(void*)*3 + 3);
v_ref_2585_ = l_Lean_replaceRef(v_ref_2574_, v_ref_2581_);
lean_inc(v_currRecDepth_2580_);
lean_inc_ref(v_toCold_2579_);
v___x_2586_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2586_, 0, v_toCold_2579_);
lean_ctor_set(v___x_2586_, 1, v_currRecDepth_2580_);
lean_ctor_set(v___x_2586_, 2, v_ref_2585_);
lean_ctor_set_uint16(v___x_2586_, sizeof(void*)*3, v_optionFlags_2582_);
lean_ctor_set_uint8(v___x_2586_, sizeof(void*)*3 + 2, v_suppressElabErrors_2583_);
lean_ctor_set_uint8(v___x_2586_, sizeof(void*)*3 + 3, v_isRecordingDeps_2584_);
v___x_2587_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_msg_2575_, v___x_2586_, v___y_2577_);
lean_dec_ref_known(v___x_2586_, 3);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2588_, lean_object* v_msg_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_2588_, v_msg_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v_ref_2588_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(lean_object* v_ref_2594_, lean_object* v_msg_2595_, lean_object* v_declHint_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v___x_2600_; lean_object* v_a_2601_; lean_object* v___x_2602_; 
v___x_2600_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_2595_, v_declHint_2596_, v___y_2597_, v___y_2598_);
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref(v___x_2600_);
v___x_2602_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_2594_, v_a_2601_, v___y_2597_, v___y_2598_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2603_, lean_object* v_msg_2604_, lean_object* v_declHint_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_2603_, v_msg_2604_, v_declHint_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v_ref_2603_);
return v_res_2609_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2612_ = l_Lean_stringToMessageData(v___x_2611_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2613_, lean_object* v_constName_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; uint8_t v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2618_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2619_ = 0;
lean_inc(v_constName_2614_);
v___x_2620_ = l_Lean_MessageData_ofConstName(v_constName_2614_, v___x_2619_);
v___x_2621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2618_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
v___x_2622_ = lean_obj_once(&l_Lean_Compiler_LCNF_nameToImpureType___closed__1, &l_Lean_Compiler_LCNF_nameToImpureType___closed__1_once, _init_l_Lean_Compiler_LCNF_nameToImpureType___closed__1);
v___x_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2621_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_2613_, v___x_2623_, v_constName_2614_, v___y_2615_, v___y_2616_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2625_, lean_object* v_constName_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(v_ref_2625_, v_constName_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v_ref_2625_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(lean_object* v_constName_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v_ref_2635_; lean_object* v___x_2636_; 
v_ref_2635_ = lean_ctor_get(v___y_2632_, 2);
v___x_2636_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(v_ref_2635_, v_constName_2631_, v___y_2632_, v___y_2633_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(v_constName_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0(lean_object* v_constName_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; lean_object* v_env_2647_; uint8_t v___x_2648_; lean_object* v___x_2649_; 
v___x_2646_ = lean_st_ref_get(v___y_2644_);
v_env_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc_ref(v_env_2647_);
lean_dec(v___x_2646_);
v___x_2648_ = 0;
lean_inc(v_constName_2642_);
v___x_2649_ = l_Lean_Environment_find_x3f(v_env_2647_, v_constName_2642_, v___x_2648_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(v_constName_2642_, v___y_2643_, v___y_2644_);
return v___x_2650_;
}
else
{
lean_object* v_val_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec(v_constName_2642_);
v_val_2651_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2649_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_val_2651_);
lean_dec(v___x_2649_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
lean_ctor_set_tag(v___x_2653_, 0);
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_val_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0___boxed(lean_object* v_constName_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0(v_constName_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
return v_res_2663_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2665_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__2));
v___x_2666_ = lean_unsigned_to_nat(49u);
v___x_2667_ = lean_unsigned_to_nat(303u);
v___x_2668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__0));
v___x_2669_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__3___redArg___closed__0));
v___x_2670_ = l_mkPanicMessageWithDecl(v___x_2669_, v___x_2668_, v___x_2667_, v___x_2666_, v___x_2665_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4(lean_object* v_as_2671_, size_t v_sz_2672_, size_t v_i_2673_, lean_object* v_b_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_a_2679_; uint8_t v___x_2683_; 
v___x_2683_ = lean_usize_dec_lt(v_i_2673_, v_sz_2672_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; 
v___x_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2684_, 0, v_b_2674_);
return v___x_2684_;
}
else
{
lean_object* v___x_2685_; lean_object* v_a_2686_; lean_object* v___x_2687_; 
v___x_2685_ = lean_box(0);
v_a_2686_ = lean_array_uget_borrowed(v_as_2671_, v_i_2673_);
lean_inc(v_a_2686_);
v___x_2687_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0(v_a_2686_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___x_2687_, 1);
if (lean_obj_tag(v_a_2688_) == 5)
{
lean_object* v_val_2689_; lean_object* v_ctors_2690_; lean_object* v___x_2691_; 
v_val_2689_ = lean_ctor_get(v_a_2688_, 0);
lean_inc_ref(v_val_2689_);
lean_dec_ref_known(v_a_2688_, 1);
v_ctors_2690_ = lean_ctor_get(v_val_2689_, 4);
lean_inc(v_ctors_2690_);
lean_dec_ref(v_val_2689_);
v___x_2691_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(v_ctors_2690_, v___x_2685_, v___y_2675_, v___y_2676_);
lean_dec(v_ctors_2690_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_dec_ref_known(v___x_2691_, 1);
v_a_2679_ = v___x_2685_;
goto v___jp_2678_;
}
else
{
return v___x_2691_;
}
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_dec(v_a_2688_);
v___x_2692_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___closed__1);
v___x_2693_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_computeImpureType_spec__0(v___x_2692_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_dec_ref_known(v___x_2693_, 1);
v_a_2679_ = v___x_2685_;
goto v___jp_2678_;
}
else
{
return v___x_2693_;
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
v_a_2694_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2687_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2687_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
v___jp_2678_:
{
size_t v___x_2680_; size_t v___x_2681_; 
v___x_2680_ = ((size_t)1ULL);
v___x_2681_ = lean_usize_add(v_i_2673_, v___x_2680_);
v_i_2673_ = v___x_2681_;
v_b_2674_ = v_a_2679_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4___boxed(lean_object* v_as_2702_, lean_object* v_sz_2703_, lean_object* v_i_2704_, lean_object* v_b_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
size_t v_sz_boxed_2709_; size_t v_i_boxed_2710_; lean_object* v_res_2711_; 
v_sz_boxed_2709_ = lean_unbox_usize(v_sz_2703_);
lean_dec(v_sz_2703_);
v_i_boxed_2710_ = lean_unbox_usize(v_i_2704_);
lean_dec(v_i_2704_);
v_res_2711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4(v_as_2702_, v_sz_boxed_2709_, v_i_boxed_2710_, v_b_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec_ref(v_as_2702_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3(lean_object* v_as_2712_, size_t v_sz_2713_, size_t v_i_2714_, lean_object* v_b_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
uint8_t v___x_2719_; 
v___x_2719_ = lean_usize_dec_lt(v_i_2714_, v_sz_2713_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2720_; 
v___x_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_b_2715_);
return v___x_2720_;
}
else
{
lean_object* v___x_2721_; lean_object* v_a_2722_; lean_object* v___x_2723_; 
v___x_2721_ = lean_box(0);
v_a_2722_ = lean_array_uget_borrowed(v_as_2712_, v_i_2714_);
lean_inc(v_a_2722_);
v___x_2723_ = l_Lean_Compiler_LCNF_setOtherDeclMonoType(v_a_2722_, v___y_2716_, v___y_2717_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v___x_2724_; 
lean_dec_ref_known(v___x_2723_, 1);
lean_inc(v_a_2722_);
v___x_2724_ = l_Lean_Compiler_LCNF_setImpureType(v_a_2722_, v___y_2716_, v___y_2717_);
if (lean_obj_tag(v___x_2724_) == 0)
{
size_t v___x_2725_; size_t v___x_2726_; 
lean_dec_ref_known(v___x_2724_, 1);
v___x_2725_ = ((size_t)1ULL);
v___x_2726_ = lean_usize_add(v_i_2714_, v___x_2725_);
v_i_2714_ = v___x_2726_;
v_b_2715_ = v___x_2721_;
goto _start;
}
else
{
return v___x_2724_;
}
}
else
{
return v___x_2723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3___boxed(lean_object* v_as_2728_, lean_object* v_sz_2729_, lean_object* v_i_2730_, lean_object* v_b_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
size_t v_sz_boxed_2735_; size_t v_i_boxed_2736_; lean_object* v_res_2737_; 
v_sz_boxed_2735_ = lean_unbox_usize(v_sz_2729_);
lean_dec(v_sz_2729_);
v_i_boxed_2736_ = lean_unbox_usize(v_i_2730_);
lean_dec(v_i_2730_);
v_res_2737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3(v_as_2728_, v_sz_boxed_2735_, v_i_boxed_2736_, v_b_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v_as_2728_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(lean_object* v_as_2738_, size_t v_i_2739_, size_t v_stop_2740_, lean_object* v_b_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v_a_2745_; uint8_t v___x_2749_; 
v___x_2749_ = lean_usize_dec_eq(v_i_2739_, v_stop_2740_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v_env_2752_; lean_object* v___x_2753_; 
v___x_2750_ = lean_array_uget_borrowed(v_as_2738_, v_i_2739_);
v___x_2751_ = lean_st_ref_get(v___y_2742_);
v_env_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc_ref(v_env_2752_);
lean_dec(v___x_2751_);
lean_inc(v___x_2750_);
v___x_2753_ = l_Lean_Environment_find_x3f(v_env_2752_, v___x_2750_, v___x_2749_);
if (lean_obj_tag(v___x_2753_) == 1)
{
lean_object* v_val_2754_; 
v_val_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_val_2754_);
lean_dec_ref_known(v___x_2753_, 1);
if (lean_obj_tag(v_val_2754_) == 5)
{
lean_object* v___x_2755_; 
lean_dec_ref_known(v_val_2754_, 1);
lean_inc(v___x_2750_);
v___x_2755_ = lean_array_push(v_b_2741_, v___x_2750_);
v_a_2745_ = v___x_2755_;
goto v___jp_2744_;
}
else
{
lean_dec(v_val_2754_);
v_a_2745_ = v_b_2741_;
goto v___jp_2744_;
}
}
else
{
lean_dec(v___x_2753_);
v_a_2745_ = v_b_2741_;
goto v___jp_2744_;
}
}
else
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2756_, 0, v_b_2741_);
return v___x_2756_;
}
v___jp_2744_:
{
size_t v___x_2746_; size_t v___x_2747_; 
v___x_2746_ = ((size_t)1ULL);
v___x_2747_ = lean_usize_add(v_i_2739_, v___x_2746_);
v_i_2739_ = v___x_2747_;
v_b_2741_ = v_a_2745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg___boxed(lean_object* v_as_2757_, lean_object* v_i_2758_, lean_object* v_stop_2759_, lean_object* v_b_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
size_t v_i_boxed_2763_; size_t v_stop_boxed_2764_; lean_object* v_res_2765_; 
v_i_boxed_2763_ = lean_unbox_usize(v_i_2758_);
lean_dec(v_i_2758_);
v_stop_boxed_2764_ = lean_unbox_usize(v_stop_2759_);
lean_dec(v_stop_2759_);
v_res_2765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_as_2757_, v_i_boxed_2763_, v_stop_boxed_2764_, v_b_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v_as_2757_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compileInductives(lean_object* v_typeNames_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v_a_2773_; lean_object* v___y_2789_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2799_ = lean_unsigned_to_nat(0u);
v___x_2800_ = lean_array_get_size(v_typeNames_2768_);
v___x_2801_ = ((lean_object*)(l_Lean_Compiler_LCNF_compileInductives___closed__0));
v___x_2802_ = lean_nat_dec_lt(v___x_2799_, v___x_2800_);
if (v___x_2802_ == 0)
{
v_a_2773_ = v___x_2801_;
goto v___jp_2772_;
}
else
{
uint8_t v___x_2803_; 
v___x_2803_ = lean_nat_dec_le(v___x_2800_, v___x_2800_);
if (v___x_2803_ == 0)
{
if (v___x_2802_ == 0)
{
v_a_2773_ = v___x_2801_;
goto v___jp_2772_;
}
else
{
size_t v___x_2804_; size_t v___x_2805_; lean_object* v___x_2806_; 
v___x_2804_ = ((size_t)0ULL);
v___x_2805_ = lean_usize_of_nat(v___x_2800_);
v___x_2806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_typeNames_2768_, v___x_2804_, v___x_2805_, v___x_2801_, v_a_2770_);
v___y_2789_ = v___x_2806_;
goto v___jp_2788_;
}
}
else
{
size_t v___x_2807_; size_t v___x_2808_; lean_object* v___x_2809_; 
v___x_2807_ = ((size_t)0ULL);
v___x_2808_ = lean_usize_of_nat(v___x_2800_);
v___x_2809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_typeNames_2768_, v___x_2807_, v___x_2808_, v___x_2801_, v_a_2770_);
v___y_2789_ = v___x_2809_;
goto v___jp_2788_;
}
}
v___jp_2772_:
{
lean_object* v___x_2774_; size_t v_sz_2775_; size_t v___x_2776_; lean_object* v___x_2777_; 
v___x_2774_ = lean_box(0);
v_sz_2775_ = lean_array_size(v_a_2773_);
v___x_2776_ = ((size_t)0ULL);
v___x_2777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__2(v_a_2773_, v_sz_2775_, v___x_2776_, v___x_2774_, v_a_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v___x_2778_; 
lean_dec_ref_known(v___x_2777_, 1);
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__3(v_a_2773_, v_sz_2775_, v___x_2776_, v___x_2774_, v_a_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v___x_2779_; 
lean_dec_ref_known(v___x_2778_, 1);
v___x_2779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__4(v_a_2773_, v_sz_2775_, v___x_2776_, v___x_2774_, v_a_2769_, v_a_2770_);
lean_dec_ref(v_a_2773_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2786_ == 0)
{
lean_object* v_unused_2787_; 
v_unused_2787_ = lean_ctor_get(v___x_2779_, 0);
lean_dec(v_unused_2787_);
v___x_2781_ = v___x_2779_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_dec(v___x_2779_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2774_);
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2774_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
else
{
return v___x_2779_;
}
}
else
{
lean_dec_ref(v_a_2773_);
return v___x_2778_;
}
}
else
{
lean_dec_ref(v_a_2773_);
return v___x_2777_;
}
}
v___jp_2788_:
{
if (lean_obj_tag(v___y_2789_) == 0)
{
lean_object* v_a_2790_; 
v_a_2790_ = lean_ctor_get(v___y_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___y_2789_, 1);
v_a_2773_ = v_a_2790_;
goto v___jp_2772_;
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
v_a_2791_ = lean_ctor_get(v___y_2789_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___y_2789_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___y_2789_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___y_2789_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compileInductives___boxed(lean_object* v_typeNames_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_Compiler_LCNF_compileInductives(v_typeNames_2810_, v_a_2811_, v_a_2812_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
lean_dec_ref(v_typeNames_2810_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1(lean_object* v_as_2815_, lean_object* v_as_x27_2816_, lean_object* v_b_2817_, lean_object* v_a_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___redArg(v_as_x27_2816_, v_b_2817_, v___y_2819_, v___y_2820_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1___boxed(lean_object* v_as_2823_, lean_object* v_as_x27_2824_, lean_object* v_b_2825_, lean_object* v_a_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_compileInductives_spec__1(v_as_2823_, v_as_x27_2824_, v_b_2825_, v_a_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v_as_x27_2824_);
lean_dec(v_as_2823_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5(lean_object* v_as_2831_, size_t v_i_2832_, size_t v_stop_2833_, lean_object* v_b_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___redArg(v_as_2831_, v_i_2832_, v_stop_2833_, v_b_2834_, v___y_2836_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5___boxed(lean_object* v_as_2839_, lean_object* v_i_2840_, lean_object* v_stop_2841_, lean_object* v_b_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
size_t v_i_boxed_2846_; size_t v_stop_boxed_2847_; lean_object* v_res_2848_; 
v_i_boxed_2846_ = lean_unbox_usize(v_i_2840_);
lean_dec(v_i_2840_);
v_stop_boxed_2847_ = lean_unbox_usize(v_stop_2841_);
lean_dec(v_stop_2841_);
v_res_2848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_compileInductives_spec__5(v_as_2839_, v_i_boxed_2846_, v_stop_boxed_2847_, v_b_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec_ref(v_as_2839_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0(lean_object* v_00_u03b1_2849_, lean_object* v_constName_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___redArg(v_constName_2850_, v___y_2851_, v___y_2852_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2855_, lean_object* v_constName_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0(v_00_u03b1_2855_, v_constName_2856_, v___y_2857_, v___y_2858_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2861_, lean_object* v_ref_2862_, lean_object* v_constName_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___redArg(v_ref_2862_, v_constName_2863_, v___y_2864_, v___y_2865_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2868_, lean_object* v_ref_2869_, lean_object* v_constName_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1(v_00_u03b1_2868_, v_ref_2869_, v_constName_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v_ref_2869_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b1_2875_, lean_object* v_ref_2876_, lean_object* v_msg_2877_, lean_object* v_declHint_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_2876_, v_msg_2877_, v_declHint_2878_, v___y_2879_, v___y_2880_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7___boxed(lean_object* v_00_u03b1_2883_, lean_object* v_ref_2884_, lean_object* v_msg_2885_, lean_object* v_declHint_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7(v_00_u03b1_2883_, v_ref_2884_, v_msg_2885_, v_declHint_2886_, v___y_2887_, v___y_2888_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v_ref_2884_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(lean_object* v_msg_2891_, lean_object* v_declHint_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_2891_, v_declHint_2892_, v___y_2894_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2897_, lean_object* v_declHint_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(v_msg_2897_, v_declHint_2898_, v___y_2899_, v___y_2900_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_2903_, lean_object* v_ref_2904_, lean_object* v_msg_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_2904_, v_msg_2905_, v___y_2906_, v___y_2907_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2910_, lean_object* v_ref_2911_, lean_object* v_msg_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_compileInductives_spec__0_spec__0_spec__1_spec__7_spec__9(v_00_u03b1_2910_, v_ref_2911_, v_msg_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v_ref_2911_);
return v_res_2916_;
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
