// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.BVDecide
// Imports: import Lean.Elab.Tactic.Grind.Basic import Lean.Meta.Tactic.BVDecide.Main import Lean.Elab.Tactic.BVDecide import Lean.Meta.Tactic.BVDecide.Normalize import Lean.Meta.Tactic.Grind.BVDecide.Types
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
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_create_tempfile();
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 16, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bvDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__4_value),LEAN_SCALAR_PTR_LITERAL(184, 150, 103, 35, 70, 25, 10, 148)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__6_value),LEAN_SCALAR_PTR_LITERAL(33, 50, 202, 5, 86, 233, 189, 240)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__8_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvTypes"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__10_value),LEAN_SCALAR_PTR_LITERAL(133, 159, 97, 61, 240, 205, 127, 31)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__5_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__6_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(246, 172, 74, 48, 93, 132, 233, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(159, 125, 89, 202, 91, 47, 27, 99)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 43, 102, 233, 206, 49, 244, 172)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(48, 28, 174, 40, 141, 254, 11, 23)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 205, 242, 16, 234, 190, 33, 47)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(219, 17, 49, 200, 191, 147, 94, 212)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalBvDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(245, 19, 110, 32, 0, 147, 105, 99)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 142, 92, 236, 193, 5, 157, 115)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "bv_decide\?"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 224, 172, 67, 205, 21, 228, 63)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bvNormalize"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value),LEAN_SCALAR_PTR_LITERAL(42, 26, 136, 123, 235, 182, 158, 80)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12;
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvCheck"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__15_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__15_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__14_value),LEAN_SCALAR_PTR_LITERAL(39, 89, 115, 113, 62, 113, 141, 105)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bv_check"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalBvTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 31, 96, 242, 225, 204, 89, 193)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around."};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__16_value),LEAN_SCALAR_PTR_LITERAL(150, 149, 7, 180, 70, 199, 193, 180)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalBvCheck"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 159, 63, 127, 180, 167, 31, 248)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5;
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9_value),LEAN_SCALAR_PTR_LITERAL(107, 250, 93, 18, 255, 117, 252, 211)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`bv_normalize` failed to close the goal"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalBVNormalize"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 164, 205, 143, 231, 178, 56, 148)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___boxed(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Elab.Tactic.Grind.BVDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "_private.Lean.Elab.Tactic.Grind.BVDecide.0.Lean.Elab.Tactic.Grind.evalBVPush"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bvDecidePush"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 198, 224, 172, 164, 17, 35, 6)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "bv_decide_push"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(186, 213, 41, 102, 56, 1, 176, 57)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalBVPush"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 92, 190, 201, 240, 246, 88, 127)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(lean_object* v_cfg_7_, lean_object* v_goal_8_, lean_object* v_elaborator_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
uint8_t v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_13_ = 1;
v___x_14_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___closed__0));
v___x_15_ = lean_box(0);
v___x_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_16_, 0, v_goal_8_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
v___x_17_ = lean_st_mk_ref(v___x_16_);
v___x_18_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_18_, 0, v_elaborator_9_);
lean_ctor_set_uint8(v___x_18_, sizeof(void*)*1, v___x_13_);
v___x_19_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_7_, v___x_14_, v___x_13_, v___x_18_, v_a_10_, v_a_11_);
lean_dec_ref_known(v___x_18_, 1);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_28_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_28_ == 0)
{
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v___x_26_; 
v___x_24_ = lean_st_ref_get(v___x_17_);
lean_dec(v___x_17_);
lean_dec(v___x_24_);
if (v_isShared_23_ == 0)
{
v___x_26_ = v___x_22_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_20_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
else
{
lean_dec(v___x_17_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___boxed(lean_object* v_cfg_29_, lean_object* v_goal_30_, lean_object* v_elaborator_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_29_, v_goal_30_, v_elaborator_31_, v_a_32_, v_a_33_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig(lean_object* v_cfg_36_, lean_object* v_goal_37_, lean_object* v_elaborator_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_36_, v_goal_37_, v_elaborator_38_, v_a_43_, v_a_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___boxed(lean_object* v_cfg_47_, lean_object* v_goal_48_, lean_object* v_elaborator_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig(v_cfg_47_, v_goal_48_, v_elaborator_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
return v_res_57_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_box(0);
v___x_59_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg(){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0);
v___x_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___boxed(lean_object* v___y_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0(lean_object* v_00_u03b1_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___boxed(lean_object* v_00_u03b1_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0(v_00_u03b1_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(lean_object* v_snd_88_, lean_object* v___y_89_, lean_object* v_a_x3f_90_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_io_remove_file(v_snd_88_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_113_; 
v_a_101_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_113_ == 0)
{
v___x_103_ = v___x_92_;
v_isShared_104_ = v_isSharedCheck_113_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_92_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_113_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v_ref_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
v_ref_105_ = lean_ctor_get(v___y_89_, 4);
v___x_106_ = lean_io_error_to_string(v_a_101_);
v___x_107_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
v___x_108_ = l_Lean_MessageData_ofFormat(v___x_107_);
lean_inc(v_ref_105_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v_ref_105_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_109_);
v___x_111_ = v___x_103_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object* v_snd_114_, lean_object* v___y_115_, lean_object* v_a_x3f_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_114_, v___y_115_, v_a_x3f_116_);
lean_dec(v_a_x3f_116_);
lean_dec_ref(v___y_115_);
lean_dec_ref(v_snd_114_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(lean_object* v_f_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v_fst_131_; lean_object* v_snd_132_; lean_object* v_r_133_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_a_130_);
lean_dec_ref_known(v___x_129_, 1);
v_fst_131_ = lean_ctor_get(v_a_130_, 0);
lean_inc(v_fst_131_);
v_snd_132_ = lean_ctor_get(v_a_130_, 1);
lean_inc_n(v_snd_132_, 2);
lean_dec(v_a_130_);
lean_inc(v___y_127_);
lean_inc_ref(v___y_126_);
lean_inc(v___y_125_);
lean_inc_ref(v___y_124_);
lean_inc(v___y_123_);
lean_inc_ref(v___y_122_);
lean_inc(v___y_121_);
lean_inc_ref(v___y_120_);
v_r_133_ = lean_apply_11(v_f_119_, v_fst_131_, v_snd_132_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, lean_box(0));
if (lean_obj_tag(v_r_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_158_; 
v_a_134_ = lean_ctor_get(v_r_133_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v_r_133_);
if (v_isSharedCheck_158_ == 0)
{
v___x_136_ = v_r_133_;
v_isShared_137_ = v_isSharedCheck_158_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v_r_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_158_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
lean_inc(v_a_134_);
if (v_isShared_137_ == 0)
{
lean_ctor_set_tag(v___x_136_, 1);
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_157_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; 
v___x_140_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_132_, v___y_126_, v___x_139_);
lean_dec_ref(v___x_139_);
lean_dec(v_snd_132_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; 
v_unused_148_ = lean_ctor_get(v___x_140_, 0);
lean_dec(v_unused_148_);
v___x_142_ = v___x_140_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_dec(v___x_140_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v_a_134_);
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_134_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_dec(v_a_134_);
v_a_149_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_140_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_140_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_a_159_ = lean_ctor_get(v_r_133_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v_r_133_, 1);
v___x_160_ = lean_box(0);
v___x_161_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_132_, v___y_126_, v___x_160_);
lean_dec(v_snd_132_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_168_ == 0)
{
lean_object* v_unused_169_; 
v_unused_169_ = lean_ctor_get(v___x_161_, 0);
lean_dec(v_unused_169_);
v___x_163_ = v___x_161_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_dec(v___x_161_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
lean_ctor_set_tag(v___x_163_, 1);
lean_ctor_set(v___x_163_, 0, v_a_159_);
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_159_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
lean_dec(v_a_159_);
v_a_170_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_161_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_161_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_190_; 
lean_dec_ref(v_f_119_);
v_a_178_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_190_ == 0)
{
v___x_180_ = v___x_129_;
v_isShared_181_ = v_isSharedCheck_190_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_129_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_190_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_ref_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v_ref_182_ = lean_ctor_get(v___y_126_, 4);
v___x_183_ = lean_io_error_to_string(v_a_178_);
v___x_184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
v___x_185_ = l_Lean_MessageData_ofFormat(v___x_184_);
lean_inc(v_ref_182_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v_ref_182_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_186_);
v___x_188_ = v___x_180_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___boxed(lean_object* v_f_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(v_f_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1(lean_object* v_00_u03b1_202_, lean_object* v_f_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(v_f_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___boxed(lean_object* v_00_u03b1_214_, lean_object* v_f_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1(v_00_u03b1_214_, v_f_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0(lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_x_229_, lean_object* v_lratFile_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v_lratFile_230_, v_a_226_, v_a_227_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v_a_228_);
v___x_243_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_243_, 0, v___x_242_);
lean_closure_set(v___x_243_, 1, v_a_241_);
v___x_244_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_243_, v___y_231_, v___y_232_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec_ref_known(v___x_244_, 1);
v___x_245_ = lean_box(0);
v___x_246_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_245_, v___y_232_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
return v___x_246_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_244_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_244_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref(v_a_228_);
v_a_255_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_240_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_240_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0___boxed(lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_x_266_, lean_object* v_lratFile_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0(v_a_263_, v_a_264_, v_a_265_, v_x_266_, v_lratFile_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v_x_266_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide(lean_object* v_x_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5));
lean_inc(v_x_304_);
v___x_315_ = l_Lean_Syntax_isOfKind(v_x_304_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_dec(v_x_304_);
v___x_316_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_316_;
}
else
{
lean_object* v___x_317_; lean_object* v_cfg_318_; lean_object* v_types_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_317_ = lean_unsigned_to_nat(1u);
v_cfg_318_ = l_Lean_Syntax_getArg(v_x_304_, v___x_317_);
v___x_364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfg_318_);
v___x_365_ = l_Lean_Syntax_isOfKind(v_cfg_318_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec(v_cfg_318_);
lean_dec(v_x_304_);
v___x_366_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_366_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_367_ = lean_unsigned_to_nat(2u);
v___x_368_ = l_Lean_Syntax_getArg(v_x_304_, v___x_367_);
lean_dec(v_x_304_);
v___x_369_ = l_Lean_Syntax_isNone(v___x_368_);
if (v___x_369_ == 0)
{
uint8_t v___x_370_; 
lean_inc(v___x_368_);
v___x_370_ = l_Lean_Syntax_matchesNull(v___x_368_, v___x_317_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec(v___x_368_);
lean_dec(v_cfg_318_);
v___x_371_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_371_;
}
else
{
lean_object* v___x_372_; lean_object* v_types_373_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v_types_373_ = l_Lean_Syntax_getArg(v___x_368_, v___x_372_);
lean_dec(v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_types_373_);
v___x_377_ = l_Lean_Syntax_isOfKind(v_types_373_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
lean_dec(v_types_373_);
lean_dec(v_cfg_318_);
v___x_378_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_378_;
}
else
{
goto v___jp_374_;
}
}
else
{
goto v___jp_374_;
}
v___jp_374_:
{
lean_object* v___x_375_; 
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v_types_373_);
v_types_320_ = v___x_375_;
v___y_321_ = v_a_305_;
v___y_322_ = v_a_306_;
v___y_323_ = v_a_307_;
v___y_324_ = v_a_308_;
v___y_325_ = v_a_309_;
v___y_326_ = v_a_310_;
v___y_327_ = v_a_311_;
v___y_328_ = v_a_312_;
goto v___jp_319_;
}
}
}
else
{
lean_object* v___x_379_; 
lean_dec(v___x_368_);
v___x_379_ = lean_box(0);
v_types_320_ = v___x_379_;
v___y_321_ = v_a_305_;
v___y_322_ = v_a_306_;
v___y_323_ = v_a_307_;
v___y_324_ = v_a_308_;
v___y_325_ = v_a_309_;
v___y_326_ = v_a_310_;
v___y_327_ = v_a_311_;
v___y_328_ = v_a_312_;
goto v___jp_319_;
}
}
v___jp_319_:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v___x_330_; 
lean_dec_ref_known(v___x_329_, 1);
v___x_330_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_322_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v_mvarId_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
v_mvarId_332_ = lean_ctor_get(v_a_331_, 1);
v___x_333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__7));
lean_inc(v_mvarId_332_);
v___x_334_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_318_, v_mvarId_332_, v___x_333_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_336_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_334_, 1);
v___x_336_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_320_, v_a_335_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___f_338_; lean_object* v___x_339_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
v___f_338_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0___boxed), 14, 3);
lean_closure_set(v___f_338_, 0, v_a_335_);
lean_closure_set(v___f_338_, 1, v_a_337_);
lean_closure_set(v___f_338_, 2, v_a_331_);
v___x_339_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(v___f_338_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
return v___x_339_;
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_a_335_);
lean_dec(v_a_331_);
v_a_340_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_336_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_336_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_a_331_);
lean_dec(v_types_320_);
v_a_348_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_334_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_334_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_types_320_);
lean_dec(v_cfg_318_);
v_a_356_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_330_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_330_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_dec(v_types_320_);
lean_dec(v_cfg_318_);
return v___x_329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___boxed(lean_object* v_x_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide(v_x_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1(){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_432_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_433_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5));
v___x_434_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__15));
v___x_435_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___boxed), 10, 0);
v___x_436_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_432_, v___x_433_, v___x_434_, v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___boxed(lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1();
return v_res_438_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12(void){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Array_mkArray0(lean_box(0));
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace(lean_object* v_x_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1));
lean_inc(v_x_475_);
v___x_494_ = l_Lean_Syntax_isOfKind(v_x_475_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
lean_dec(v_x_475_);
v___x_495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_495_;
}
else
{
lean_object* v___x_496_; lean_object* v_cfgStx_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_496_ = lean_unsigned_to_nat(1u);
v_cfgStx_497_ = l_Lean_Syntax_getArg(v_x_475_, v___x_496_);
v___x_498_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfgStx_497_);
v___x_499_ = l_Lean_Syntax_isOfKind(v_cfgStx_497_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
lean_dec(v_cfgStx_497_);
lean_dec(v_x_475_);
v___x_500_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_500_;
}
else
{
lean_object* v___x_501_; lean_object* v_tk_502_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v_typesStx_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_501_ = lean_unsigned_to_nat(0u);
v_tk_502_ = l_Lean_Syntax_getArg(v_x_475_, v___x_501_);
v___x_653_ = lean_unsigned_to_nat(2u);
v___x_654_ = l_Lean_Syntax_getArg(v_x_475_, v___x_653_);
lean_dec(v_x_475_);
v___x_655_ = l_Lean_Syntax_isNone(v___x_654_);
if (v___x_655_ == 0)
{
uint8_t v___x_656_; 
lean_inc(v___x_654_);
v___x_656_ = l_Lean_Syntax_matchesNull(v___x_654_, v___x_496_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
lean_dec(v___x_654_);
lean_dec(v_tk_502_);
lean_dec(v_cfgStx_497_);
v___x_657_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_657_;
}
else
{
lean_object* v_typesStx_658_; 
v_typesStx_658_ = l_Lean_Syntax_getArg(v___x_654_, v___x_501_);
lean_dec(v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_typesStx_658_);
v___x_662_ = l_Lean_Syntax_isOfKind(v_typesStx_658_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_dec(v_typesStx_658_);
lean_dec(v_tk_502_);
lean_dec(v_cfgStx_497_);
v___x_663_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_663_;
}
else
{
goto v___jp_659_;
}
}
else
{
goto v___jp_659_;
}
v___jp_659_:
{
lean_object* v___x_660_; 
v___x_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_660_, 0, v_typesStx_658_);
v_typesStx_557_ = v___x_660_;
v___y_558_ = v_a_476_;
v___y_559_ = v_a_477_;
v___y_560_ = v_a_478_;
v___y_561_ = v_a_479_;
v___y_562_ = v_a_480_;
v___y_563_ = v_a_481_;
v___y_564_ = v_a_482_;
v___y_565_ = v_a_483_;
goto v___jp_556_;
}
}
}
else
{
lean_object* v___x_664_; 
lean_dec(v___x_654_);
v___x_664_ = lean_box(0);
v_typesStx_557_ = v___x_664_;
v___y_558_ = v_a_476_;
v___y_559_ = v_a_477_;
v___y_560_ = v_a_478_;
v___y_561_ = v_a_479_;
v___y_562_ = v_a_480_;
v___y_563_ = v_a_481_;
v___y_564_ = v_a_482_;
v___y_565_ = v_a_483_;
goto v___jp_556_;
}
v___jp_503_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_inc_ref(v___y_509_);
v___x_517_ = l_Array_append___redArg(v___y_509_, v___y_516_);
lean_dec_ref(v___y_516_);
lean_inc(v___y_506_);
lean_inc(v___y_511_);
v___x_518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_518_, 0, v___y_511_);
lean_ctor_set(v___x_518_, 1, v___y_506_);
lean_ctor_set(v___x_518_, 2, v___x_517_);
lean_inc(v___y_507_);
v___x_519_ = l_Lean_Syntax_node3(v___y_511_, v___y_507_, v___y_504_, v_cfgStx_497_, v___x_518_);
lean_inc(v___y_505_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___y_505_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_box(0);
v___x_522_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
lean_ctor_set(v___x_522_, 2, v___x_521_);
lean_ctor_set(v___x_522_, 3, v___x_521_);
lean_ctor_set(v___x_522_, 4, v___x_521_);
lean_ctor_set(v___x_522_, 5, v___x_521_);
lean_inc(v___y_514_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v___y_514_);
v___x_524_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_525_ = 4;
v___x_526_ = l_Lean_MessageData_nil;
v___x_527_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_502_, v___x_522_, v___x_523_, v___x_524_, v___x_521_, v___x_525_, v___x_526_, v___y_513_, v___y_512_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_dec_ref_known(v___x_527_, 1);
v___y_486_ = v___y_515_;
v___y_487_ = v___y_508_;
v___y_488_ = v___y_510_;
v___y_489_ = v___y_513_;
v___y_490_ = v___y_512_;
goto v___jp_485_;
}
else
{
return v___x_527_;
}
}
v___jp_528_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
lean_inc_ref(v___y_530_);
v___x_543_ = l_Array_append___redArg(v___y_530_, v___y_542_);
lean_dec_ref(v___y_542_);
lean_inc(v___y_533_);
lean_inc(v___y_531_);
v___x_544_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_544_, 0, v___y_531_);
lean_ctor_set(v___x_544_, 1, v___y_533_);
lean_ctor_set(v___x_544_, 2, v___x_543_);
v___x_545_ = lean_box(2);
v___x_546_ = l_Lean_Syntax_mkStrLit(v___y_537_, v___x_545_);
lean_inc(v___y_529_);
v___x_547_ = l_Lean_Syntax_node4(v___y_531_, v___y_529_, v___y_538_, v_cfgStx_497_, v___x_544_, v___x_546_);
lean_inc(v___y_540_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___y_540_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = lean_box(0);
v___x_550_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
lean_ctor_set(v___x_550_, 2, v___x_549_);
lean_ctor_set(v___x_550_, 3, v___x_549_);
lean_ctor_set(v___x_550_, 4, v___x_549_);
lean_ctor_set(v___x_550_, 5, v___x_549_);
lean_inc(v___y_532_);
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v___y_532_);
v___x_552_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_553_ = 4;
v___x_554_ = l_Lean_MessageData_nil;
v___x_555_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_502_, v___x_550_, v___x_551_, v___x_552_, v___x_549_, v___x_553_, v___x_554_, v___y_539_, v___y_536_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_dec_ref_known(v___x_555_, 1);
v___y_486_ = v___y_541_;
v___y_487_ = v___y_534_;
v___y_488_ = v___y_535_;
v___y_489_ = v___y_539_;
v___y_490_ = v___y_536_;
goto v___jp_485_;
}
else
{
return v___x_555_;
}
}
v___jp_556_:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_651_; 
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v___x_566_, 0);
lean_dec(v_unused_652_);
v___x_568_ = v___x_566_;
v_isShared_569_ = v_isSharedCheck_651_;
goto v_resetjp_567_;
}
else
{
lean_dec(v___x_566_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_651_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_559_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v_mvarId_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
v_mvarId_572_ = lean_ctor_get(v_a_571_, 1);
v___x_573_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__4));
lean_inc(v_mvarId_572_);
lean_inc(v_cfgStx_497_);
v___x_574_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfgStx_497_, v_mvarId_572_, v___x_573_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
lean_inc(v_typesStx_557_);
v___x_576_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_557_, v_a_575_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_578_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_576_, 1);
v___x_578_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_a_575_, v_a_577_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 1);
lean_ctor_set(v___x_568_, 0, v_a_571_);
v___x_581_ = v___x_568_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_571_);
v___x_581_ = v_reuseFailAlloc_618_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed), 12, 2);
lean_closure_set(v___x_582_, 0, v___x_581_);
lean_closure_set(v___x_582_, 1, v_a_579_);
v___x_583_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_582_, v___y_558_, v___y_559_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
if (lean_obj_tag(v_a_584_) == 0)
{
lean_object* v_ref_585_; uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_ref_585_ = lean_ctor_get(v___y_564_, 4);
v___x_586_ = 0;
v___x_587_ = l_Lean_SourceInfo_fromRef(v_ref_585_, v___x_586_);
v___x_588_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6));
v___x_589_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8));
v___x_590_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9));
lean_inc(v___x_587_);
v___x_591_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_587_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
v___x_593_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12);
if (lean_obj_tag(v_typesStx_557_) == 1)
{
lean_object* v_val_594_; lean_object* v___x_595_; 
v_val_594_ = lean_ctor_get(v_typesStx_557_, 0);
lean_inc(v_val_594_);
lean_dec_ref_known(v_typesStx_557_, 1);
v___x_595_ = l_Array_mkArray1___redArg(v_val_594_);
v___y_504_ = v___x_591_;
v___y_505_ = v___x_588_;
v___y_506_ = v___x_592_;
v___y_507_ = v___x_589_;
v___y_508_ = v___y_562_;
v___y_509_ = v___x_593_;
v___y_510_ = v___y_563_;
v___y_511_ = v___x_587_;
v___y_512_ = v___y_565_;
v___y_513_ = v___y_564_;
v___y_514_ = v_ref_585_;
v___y_515_ = v___y_559_;
v___y_516_ = v___x_595_;
goto v___jp_503_;
}
else
{
lean_object* v___x_596_; 
lean_dec(v_typesStx_557_);
v___x_596_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__13));
v___y_504_ = v___x_591_;
v___y_505_ = v___x_588_;
v___y_506_ = v___x_592_;
v___y_507_ = v___x_589_;
v___y_508_ = v___y_562_;
v___y_509_ = v___x_593_;
v___y_510_ = v___y_563_;
v___y_511_ = v___x_587_;
v___y_512_ = v___y_565_;
v___y_513_ = v___y_564_;
v___y_514_ = v_ref_585_;
v___y_515_ = v___y_559_;
v___y_516_ = v___x_596_;
goto v___jp_503_;
}
}
else
{
lean_object* v_path_597_; lean_object* v_ref_598_; uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_path_597_ = lean_ctor_get(v_a_584_, 0);
lean_inc_ref(v_path_597_);
lean_dec_ref_known(v_a_584_, 1);
v_ref_598_ = lean_ctor_get(v___y_564_, 4);
v___x_599_ = 0;
v___x_600_ = l_Lean_SourceInfo_fromRef(v_ref_598_, v___x_599_);
v___x_601_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6));
v___x_602_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__15));
v___x_603_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__16));
lean_inc(v___x_600_);
v___x_604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_600_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
v___x_606_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12);
if (lean_obj_tag(v_typesStx_557_) == 1)
{
lean_object* v_val_607_; lean_object* v___x_608_; 
v_val_607_ = lean_ctor_get(v_typesStx_557_, 0);
lean_inc(v_val_607_);
lean_dec_ref_known(v_typesStx_557_, 1);
v___x_608_ = l_Array_mkArray1___redArg(v_val_607_);
v___y_529_ = v___x_602_;
v___y_530_ = v___x_606_;
v___y_531_ = v___x_600_;
v___y_532_ = v_ref_598_;
v___y_533_ = v___x_605_;
v___y_534_ = v___y_562_;
v___y_535_ = v___y_563_;
v___y_536_ = v___y_565_;
v___y_537_ = v_path_597_;
v___y_538_ = v___x_604_;
v___y_539_ = v___y_564_;
v___y_540_ = v___x_601_;
v___y_541_ = v___y_559_;
v___y_542_ = v___x_608_;
goto v___jp_528_;
}
else
{
lean_object* v___x_609_; 
lean_dec(v_typesStx_557_);
v___x_609_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__13));
v___y_529_ = v___x_602_;
v___y_530_ = v___x_606_;
v___y_531_ = v___x_600_;
v___y_532_ = v_ref_598_;
v___y_533_ = v___x_605_;
v___y_534_ = v___y_562_;
v___y_535_ = v___y_563_;
v___y_536_ = v___y_565_;
v___y_537_ = v_path_597_;
v___y_538_ = v___x_604_;
v___y_539_ = v___y_564_;
v___y_540_ = v___x_601_;
v___y_541_ = v___y_559_;
v___y_542_ = v___x_609_;
goto v___jp_528_;
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_typesStx_557_);
lean_dec(v_tk_502_);
lean_dec(v_cfgStx_497_);
v_a_610_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_583_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_583_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec(v_a_571_);
lean_del_object(v___x_568_);
lean_dec(v_typesStx_557_);
lean_dec(v_tk_502_);
lean_dec(v_cfgStx_497_);
v_a_619_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_578_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_578_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec(v_a_575_);
lean_dec(v_a_571_);
lean_del_object(v___x_568_);
lean_dec(v_typesStx_557_);
lean_dec(v_tk_502_);
lean_dec(v_cfgStx_497_);
v_a_627_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_576_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_576_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec(v_a_571_);
lean_del_object(v___x_568_);
lean_dec(v_typesStx_557_);
lean_dec(v_tk_502_);
lean_dec(v_cfgStx_497_);
v_a_635_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_574_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_574_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_del_object(v___x_568_);
lean_dec(v_typesStx_557_);
lean_dec(v_tk_502_);
lean_dec(v_cfgStx_497_);
v_a_643_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_570_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_570_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
else
{
lean_dec(v_typesStx_557_);
lean_dec(v_tk_502_);
lean_dec(v_cfgStx_497_);
return v___x_566_;
}
}
}
}
v___jp_485_:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_box(0);
v___x_492_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_491_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed(lean_object* v_x_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace(v_x_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1(){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_681_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_682_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1));
v___x_683_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__1));
v___x_684_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed), 10, 0);
v___x_685_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_681_, v___x_682_, v___x_683_, v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___boxed(lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1();
return v_res_687_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(lean_object* v_opts_688_, lean_object* v_opt_689_){
_start:
{
lean_object* v_name_690_; lean_object* v_defValue_691_; lean_object* v_map_692_; lean_object* v___x_693_; 
v_name_690_ = lean_ctor_get(v_opt_689_, 0);
v_defValue_691_ = lean_ctor_get(v_opt_689_, 1);
v_map_692_ = lean_ctor_get(v_opts_688_, 0);
v___x_693_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_692_, v_name_690_);
if (lean_obj_tag(v___x_693_) == 0)
{
uint8_t v___x_694_; 
v___x_694_ = lean_unbox(v_defValue_691_);
return v___x_694_;
}
else
{
lean_object* v_val_695_; 
v_val_695_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_val_695_);
lean_dec_ref_known(v___x_693_, 1);
if (lean_obj_tag(v_val_695_) == 1)
{
uint8_t v_v_696_; 
v_v_696_ = lean_ctor_get_uint8(v_val_695_, 0);
lean_dec_ref_known(v_val_695_, 0);
return v_v_696_;
}
else
{
uint8_t v___x_697_; 
lean_dec(v_val_695_);
v___x_697_ = lean_unbox(v_defValue_691_);
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_698_, lean_object* v_opt_699_){
_start:
{
uint8_t v_res_700_; lean_object* v_r_701_; 
v_res_700_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(v_opts_698_, v_opt_699_);
lean_dec_ref(v_opt_699_);
lean_dec_ref(v_opts_698_);
v_r_701_ = lean_box(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_708_, uint8_t v___y_709_, lean_object* v_x_710_){
_start:
{
if (lean_obj_tag(v_x_710_) == 1)
{
lean_object* v_pre_711_; 
v_pre_711_ = lean_ctor_get(v_x_710_, 0);
switch(lean_obj_tag(v_pre_711_))
{
case 1:
{
lean_object* v_pre_712_; 
v_pre_712_ = lean_ctor_get(v_pre_711_, 0);
switch(lean_obj_tag(v_pre_712_))
{
case 0:
{
lean_object* v_str_713_; lean_object* v_str_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v_str_713_ = lean_ctor_get(v_x_710_, 1);
v_str_714_ = lean_ctor_get(v_pre_711_, 1);
v___x_715_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3));
v___x_716_ = lean_string_dec_eq(v_str_714_, v___x_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2));
v___x_718_ = lean_string_dec_eq(v_str_714_, v___x_717_);
if (v___x_718_ == 0)
{
return v___x_718_;
}
else
{
lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_719_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_720_ = lean_string_dec_eq(v_str_713_, v___x_719_);
if (v___x_720_ == 0)
{
return v___x_720_;
}
else
{
return v_suppressElabErrors_708_;
}
}
}
else
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_722_ = lean_string_dec_eq(v_str_713_, v___x_721_);
if (v___x_722_ == 0)
{
return v___x_722_;
}
else
{
return v_suppressElabErrors_708_;
}
}
}
case 1:
{
lean_object* v_pre_723_; 
v_pre_723_ = lean_ctor_get(v_pre_712_, 0);
if (lean_obj_tag(v_pre_723_) == 0)
{
lean_object* v_str_724_; lean_object* v_str_725_; lean_object* v_str_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_str_724_ = lean_ctor_get(v_x_710_, 1);
v_str_725_ = lean_ctor_get(v_pre_711_, 1);
v_str_726_ = lean_ctor_get(v_pre_712_, 1);
v___x_727_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_728_ = lean_string_dec_eq(v_str_726_, v___x_727_);
if (v___x_728_ == 0)
{
return v___x_728_;
}
else
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_730_ = lean_string_dec_eq(v_str_725_, v___x_729_);
if (v___x_730_ == 0)
{
return v___x_730_;
}
else
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_732_ = lean_string_dec_eq(v_str_724_, v___x_731_);
if (v___x_732_ == 0)
{
return v___x_732_;
}
else
{
return v_suppressElabErrors_708_;
}
}
}
}
else
{
return v___y_709_;
}
}
default: 
{
return v___y_709_;
}
}
}
case 0:
{
lean_object* v_str_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v_str_733_ = lean_ctor_get(v_x_710_, 1);
v___x_734_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_735_ = lean_string_dec_eq(v_str_733_, v___x_734_);
if (v___x_735_ == 0)
{
return v___x_735_;
}
else
{
return v_suppressElabErrors_708_;
}
}
default: 
{
return v___y_709_;
}
}
}
else
{
return v___y_709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_736_, lean_object* v___y_737_, lean_object* v_x_738_){
_start:
{
uint8_t v_suppressElabErrors_boxed_739_; uint8_t v___y_7441__boxed_740_; uint8_t v_res_741_; lean_object* v_r_742_; 
v_suppressElabErrors_boxed_739_ = lean_unbox(v_suppressElabErrors_736_);
v___y_7441__boxed_740_ = lean_unbox(v___y_737_);
v_res_741_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_739_, v___y_7441__boxed_740_, v_x_738_);
lean_dec(v_x_738_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; lean_object* v_env_750_; lean_object* v___x_751_; lean_object* v_mctx_752_; lean_object* v_lctx_753_; lean_object* v_options_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_749_ = lean_st_ref_get(v___y_747_);
v_env_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc_ref(v_env_750_);
lean_dec(v___x_749_);
v___x_751_ = lean_st_ref_get(v___y_745_);
v_mctx_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc_ref(v_mctx_752_);
lean_dec(v___x_751_);
v_lctx_753_ = lean_ctor_get(v___y_744_, 2);
v_options_754_ = lean_ctor_get(v___y_746_, 1);
lean_inc_ref(v_options_754_);
lean_inc_ref(v_lctx_753_);
v___x_755_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_755_, 0, v_env_750_);
lean_ctor_set(v___x_755_, 1, v_mctx_752_);
lean_ctor_set(v___x_755_, 2, v_lctx_753_);
lean_ctor_set(v___x_755_, 3, v_options_754_);
v___x_756_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v_msgData_743_);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v_msgData_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(lean_object* v_ref_766_, lean_object* v_msgData_767_, uint8_t v_severity_768_, uint8_t v_isSilent_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
uint8_t v___y_776_; uint8_t v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_812_; uint8_t v___y_813_; uint8_t v___y_814_; uint8_t v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_838_; uint8_t v___y_839_; uint8_t v___y_840_; uint8_t v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_848_; uint8_t v___y_849_; uint8_t v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; uint8_t v___y_853_; uint8_t v___x_858_; lean_object* v___y_860_; uint8_t v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; uint8_t v___y_864_; uint8_t v___y_865_; uint8_t v___y_867_; uint8_t v___x_881_; 
v___x_858_ = 2;
v___x_881_ = l_Lean_instBEqMessageSeverity_beq(v_severity_768_, v___x_858_);
if (v___x_881_ == 0)
{
v___y_867_ = v___x_881_;
goto v___jp_866_;
}
else
{
uint8_t v___x_882_; 
lean_inc_ref(v_msgData_767_);
v___x_882_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_767_);
v___y_867_ = v___x_882_;
goto v___jp_866_;
}
v___jp_775_:
{
lean_object* v___x_785_; lean_object* v_currNamespace_786_; lean_object* v_openDecls_787_; lean_object* v_env_788_; lean_object* v_nextMacroScope_789_; lean_object* v_ngen_790_; lean_object* v_auxDeclNGen_791_; lean_object* v_traceState_792_; lean_object* v_cache_793_; lean_object* v_messages_794_; lean_object* v_infoState_795_; lean_object* v_snapshotTasks_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_810_; 
v___x_785_ = lean_st_ref_take(v___y_784_);
v_currNamespace_786_ = lean_ctor_get(v___y_783_, 5);
v_openDecls_787_ = lean_ctor_get(v___y_783_, 6);
v_env_788_ = lean_ctor_get(v___x_785_, 0);
v_nextMacroScope_789_ = lean_ctor_get(v___x_785_, 1);
v_ngen_790_ = lean_ctor_get(v___x_785_, 2);
v_auxDeclNGen_791_ = lean_ctor_get(v___x_785_, 3);
v_traceState_792_ = lean_ctor_get(v___x_785_, 4);
v_cache_793_ = lean_ctor_get(v___x_785_, 5);
v_messages_794_ = lean_ctor_get(v___x_785_, 6);
v_infoState_795_ = lean_ctor_get(v___x_785_, 7);
v_snapshotTasks_796_ = lean_ctor_get(v___x_785_, 8);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_810_ == 0)
{
v___x_798_ = v___x_785_;
v_isShared_799_ = v_isSharedCheck_810_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_snapshotTasks_796_);
lean_inc(v_infoState_795_);
lean_inc(v_messages_794_);
lean_inc(v_cache_793_);
lean_inc(v_traceState_792_);
lean_inc(v_auxDeclNGen_791_);
lean_inc(v_ngen_790_);
lean_inc(v_nextMacroScope_789_);
lean_inc(v_env_788_);
lean_dec(v___x_785_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_810_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
lean_inc(v_openDecls_787_);
lean_inc(v_currNamespace_786_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_currNamespace_786_);
lean_ctor_set(v___x_800_, 1, v_openDecls_787_);
v___x_801_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v___y_782_);
lean_inc_ref(v___y_781_);
lean_inc_ref(v___y_778_);
v___x_802_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_802_, 0, v___y_778_);
lean_ctor_set(v___x_802_, 1, v___y_779_);
lean_ctor_set(v___x_802_, 2, v___y_780_);
lean_ctor_set(v___x_802_, 3, v___y_781_);
lean_ctor_set(v___x_802_, 4, v___x_801_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*5, v___y_777_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*5 + 1, v___y_776_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*5 + 2, v_isSilent_769_);
v___x_803_ = l_Lean_MessageLog_add(v___x_802_, v_messages_794_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 6, v___x_803_);
v___x_805_ = v___x_798_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_env_788_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_nextMacroScope_789_);
lean_ctor_set(v_reuseFailAlloc_809_, 2, v_ngen_790_);
lean_ctor_set(v_reuseFailAlloc_809_, 3, v_auxDeclNGen_791_);
lean_ctor_set(v_reuseFailAlloc_809_, 4, v_traceState_792_);
lean_ctor_set(v_reuseFailAlloc_809_, 5, v_cache_793_);
lean_ctor_set(v_reuseFailAlloc_809_, 6, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_809_, 7, v_infoState_795_);
lean_ctor_set(v_reuseFailAlloc_809_, 8, v_snapshotTasks_796_);
v___x_805_ = v_reuseFailAlloc_809_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_806_ = lean_st_ref_put(v___y_784_, v___x_805_);
v___x_807_ = lean_box(0);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
}
v___jp_811_:
{
lean_object* v_fileName_819_; lean_object* v_fileMap_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_836_; 
v_fileName_819_ = lean_ctor_get(v___y_816_, 0);
v_fileMap_820_ = lean_ctor_get(v___y_816_, 1);
v___x_821_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_767_);
v___x_822_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v___x_821_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_836_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_836_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_836_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_inc_ref_n(v_fileMap_820_, 2);
v___x_827_ = l_Lean_FileMap_toPosition(v_fileMap_820_, v___y_817_);
lean_dec(v___y_817_);
v___x_828_ = l_Lean_FileMap_toPosition(v_fileMap_820_, v___y_818_);
lean_dec(v___y_818_);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
v___x_830_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___closed__0));
if (v___y_815_ == 0)
{
lean_del_object(v___x_825_);
lean_dec_ref(v___y_812_);
v___y_776_ = v___y_813_;
v___y_777_ = v___y_814_;
v___y_778_ = v_fileName_819_;
v___y_779_ = v___x_827_;
v___y_780_ = v___x_829_;
v___y_781_ = v___x_830_;
v___y_782_ = v_a_823_;
v___y_783_ = v___y_772_;
v___y_784_ = v___y_773_;
goto v___jp_775_;
}
else
{
uint8_t v___x_831_; 
lean_inc(v_a_823_);
v___x_831_ = l_Lean_MessageData_hasTag(v___y_812_, v_a_823_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_834_; 
lean_dec_ref_known(v___x_829_, 1);
lean_dec_ref(v___x_827_);
lean_dec(v_a_823_);
v___x_832_ = lean_box(0);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_832_);
v___x_834_ = v___x_825_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
else
{
lean_del_object(v___x_825_);
v___y_776_ = v___y_813_;
v___y_777_ = v___y_814_;
v___y_778_ = v_fileName_819_;
v___y_779_ = v___x_827_;
v___y_780_ = v___x_829_;
v___y_781_ = v___x_830_;
v___y_782_ = v_a_823_;
v___y_783_ = v___y_772_;
v___y_784_ = v___y_773_;
goto v___jp_775_;
}
}
}
}
v___jp_837_:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Syntax_getTailPos_x3f(v___y_842_, v___y_840_);
lean_dec(v___y_842_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_inc(v___y_844_);
v___y_812_ = v___y_838_;
v___y_813_ = v___y_839_;
v___y_814_ = v___y_840_;
v___y_815_ = v___y_841_;
v___y_816_ = v___y_843_;
v___y_817_ = v___y_844_;
v___y_818_ = v___y_844_;
goto v___jp_811_;
}
else
{
lean_object* v_val_846_; 
v_val_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_val_846_);
lean_dec_ref_known(v___x_845_, 1);
v___y_812_ = v___y_838_;
v___y_813_ = v___y_839_;
v___y_814_ = v___y_840_;
v___y_815_ = v___y_841_;
v___y_816_ = v___y_843_;
v___y_817_ = v___y_844_;
v___y_818_ = v_val_846_;
goto v___jp_811_;
}
}
v___jp_847_:
{
lean_object* v_ref_854_; lean_object* v___x_855_; 
v_ref_854_ = l_Lean_replaceRef(v_ref_766_, v___y_852_);
v___x_855_ = l_Lean_Syntax_getPos_x3f(v_ref_854_, v___y_849_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v___x_856_; 
v___x_856_ = lean_unsigned_to_nat(0u);
v___y_838_ = v___y_848_;
v___y_839_ = v___y_853_;
v___y_840_ = v___y_849_;
v___y_841_ = v___y_850_;
v___y_842_ = v_ref_854_;
v___y_843_ = v___y_851_;
v___y_844_ = v___x_856_;
goto v___jp_837_;
}
else
{
lean_object* v_val_857_; 
v_val_857_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v___x_855_, 1);
v___y_838_ = v___y_848_;
v___y_839_ = v___y_853_;
v___y_840_ = v___y_849_;
v___y_841_ = v___y_850_;
v___y_842_ = v_ref_854_;
v___y_843_ = v___y_851_;
v___y_844_ = v_val_857_;
goto v___jp_837_;
}
}
v___jp_859_:
{
if (v___y_865_ == 0)
{
v___y_848_ = v___y_860_;
v___y_849_ = v___y_864_;
v___y_850_ = v___y_861_;
v___y_851_ = v___y_862_;
v___y_852_ = v___y_863_;
v___y_853_ = v_severity_768_;
goto v___jp_847_;
}
else
{
v___y_848_ = v___y_860_;
v___y_849_ = v___y_864_;
v___y_850_ = v___y_861_;
v___y_851_ = v___y_862_;
v___y_852_ = v___y_863_;
v___y_853_ = v___x_858_;
goto v___jp_847_;
}
}
v___jp_866_:
{
if (v___y_867_ == 0)
{
lean_object* v_toCold_868_; lean_object* v_options_869_; lean_object* v_ref_870_; uint8_t v_suppressElabErrors_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___f_874_; uint8_t v___x_875_; uint8_t v___x_876_; 
v_toCold_868_ = lean_ctor_get(v___y_772_, 0);
v_options_869_ = lean_ctor_get(v___y_772_, 1);
v_ref_870_ = lean_ctor_get(v___y_772_, 4);
v_suppressElabErrors_871_ = lean_ctor_get_uint8(v___y_772_, sizeof(void*)*10 + 1);
v___x_872_ = lean_box(v_suppressElabErrors_871_);
v___x_873_ = lean_box(v___y_867_);
v___f_874_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_874_, 0, v___x_872_);
lean_closure_set(v___f_874_, 1, v___x_873_);
v___x_875_ = 1;
v___x_876_ = l_Lean_instBEqMessageSeverity_beq(v_severity_768_, v___x_875_);
if (v___x_876_ == 0)
{
v___y_860_ = v___f_874_;
v___y_861_ = v_suppressElabErrors_871_;
v___y_862_ = v_toCold_868_;
v___y_863_ = v_ref_870_;
v___y_864_ = v___y_867_;
v___y_865_ = v___x_876_;
goto v___jp_859_;
}
else
{
lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_877_ = l_Lean_warningAsError;
v___x_878_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(v_options_869_, v___x_877_);
v___y_860_ = v___f_874_;
v___y_861_ = v_suppressElabErrors_871_;
v___y_862_ = v_toCold_868_;
v___y_863_ = v_ref_870_;
v___y_864_ = v___y_867_;
v___y_865_ = v___x_878_;
goto v___jp_859_;
}
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec_ref(v_msgData_767_);
v___x_879_ = lean_box(0);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_883_, lean_object* v_msgData_884_, lean_object* v_severity_885_, lean_object* v_isSilent_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
uint8_t v_severity_boxed_892_; uint8_t v_isSilent_boxed_893_; lean_object* v_res_894_; 
v_severity_boxed_892_ = lean_unbox(v_severity_885_);
v_isSilent_boxed_893_ = lean_unbox(v_isSilent_886_);
v_res_894_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(v_ref_883_, v_msgData_884_, v_severity_boxed_892_, v_isSilent_boxed_893_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v_ref_883_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(lean_object* v_msgData_895_, uint8_t v_severity_896_, uint8_t v_isSilent_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_ref_903_; lean_object* v___x_904_; 
v_ref_903_ = lean_ctor_get(v___y_900_, 4);
v___x_904_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(v_ref_903_, v_msgData_895_, v_severity_896_, v_isSilent_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0___boxed(lean_object* v_msgData_905_, lean_object* v_severity_906_, lean_object* v_isSilent_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
uint8_t v_severity_boxed_913_; uint8_t v_isSilent_boxed_914_; lean_object* v_res_915_; 
v_severity_boxed_913_ = lean_unbox(v_severity_906_);
v_isSilent_boxed_914_ = lean_unbox(v_isSilent_907_);
v_res_915_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(v_msgData_905_, v_severity_boxed_913_, v_isSilent_boxed_914_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(lean_object* v_msgData_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
uint8_t v___x_922_; uint8_t v___x_923_; lean_object* v___x_924_; 
v___x_922_ = 1;
v___x_923_ = 0;
v___x_924_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(v_msgData_916_, v___x_922_, v___x_923_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0___boxed(lean_object* v_msgData_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(v_msgData_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_931_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__0));
v___x_934_ = l_Lean_stringToMessageData(v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0(lean_object* v___x_935_, lean_object* v___x_936_, lean_object* v___x_937_, lean_object* v___x_938_, lean_object* v_cfgStx_939_, lean_object* v_tk_940_, lean_object* v_typesStx_941_, lean_object* v___x_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_ref_948_; uint8_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___y_959_; 
v_ref_948_ = lean_ctor_get(v___y_945_, 4);
v___x_949_ = 0;
v___x_950_ = l_Lean_SourceInfo_fromRef(v_ref_948_, v___x_949_);
v___x_951_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6));
v___x_952_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7));
v___x_953_ = l_Lean_Name_mkStr5(v___x_935_, v___x_936_, v___x_937_, v___x_938_, v___x_952_);
v___x_954_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9));
lean_inc(v___x_950_);
v___x_955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_950_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
v___x_957_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12);
if (lean_obj_tag(v_typesStx_941_) == 1)
{
lean_object* v_val_980_; lean_object* v___x_981_; 
v_val_980_ = lean_ctor_get(v_typesStx_941_, 0);
lean_inc(v_val_980_);
lean_dec_ref_known(v_typesStx_941_, 1);
v___x_981_ = l_Array_mkArray1___redArg(v_val_980_);
v___y_959_ = v___x_981_;
goto v___jp_958_;
}
else
{
lean_object* v___x_982_; 
lean_dec(v_typesStx_941_);
v___x_982_ = lean_mk_empty_array_with_capacity(v___x_942_);
v___y_959_ = v___x_982_;
goto v___jp_958_;
}
v___jp_958_:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1);
v___x_961_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(v___x_960_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_978_; 
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; 
v_unused_979_ = lean_ctor_get(v___x_961_, 0);
lean_dec(v_unused_979_);
v___x_963_ = v___x_961_;
v_isShared_964_ = v_isSharedCheck_978_;
goto v_resetjp_962_;
}
else
{
lean_dec(v___x_961_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_978_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_965_ = l_Array_append___redArg(v___x_957_, v___y_959_);
lean_dec_ref(v___y_959_);
lean_inc(v___x_950_);
v___x_966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_966_, 0, v___x_950_);
lean_ctor_set(v___x_966_, 1, v___x_956_);
lean_ctor_set(v___x_966_, 2, v___x_965_);
v___x_967_ = l_Lean_Syntax_node3(v___x_950_, v___x_953_, v___x_955_, v_cfgStx_939_, v___x_966_);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_951_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_box(0);
v___x_970_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
lean_ctor_set(v___x_970_, 2, v___x_969_);
lean_ctor_set(v___x_970_, 3, v___x_969_);
lean_ctor_set(v___x_970_, 4, v___x_969_);
lean_ctor_set(v___x_970_, 5, v___x_969_);
lean_inc(v_ref_948_);
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 1);
lean_ctor_set(v___x_963_, 0, v_ref_948_);
v___x_972_ = v___x_963_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_ref_948_);
v___x_972_ = v_reuseFailAlloc_977_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; uint8_t v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_973_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_974_ = 4;
v___x_975_ = l_Lean_MessageData_nil;
v___x_976_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_940_, v___x_970_, v___x_972_, v___x_973_, v___x_969_, v___x_974_, v___x_975_, v___y_945_, v___y_946_);
return v___x_976_;
}
}
}
else
{
lean_dec_ref(v___y_959_);
lean_dec_ref_known(v___x_955_, 2);
lean_dec(v___x_953_);
lean_dec(v___x_950_);
lean_dec(v_tk_940_);
lean_dec(v_cfgStx_939_);
return v___x_961_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___boxed(lean_object* v___x_983_, lean_object* v___x_984_, lean_object* v___x_985_, lean_object* v___x_986_, lean_object* v_cfgStx_987_, lean_object* v_tk_988_, lean_object* v_typesStx_989_, lean_object* v___x_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0(v___x_983_, v___x_984_, v___x_985_, v___x_986_, v_cfgStx_987_, v_tk_988_, v_typesStx_989_, v___x_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___x_990_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck(lean_object* v_x_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1012_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0));
v___x_1013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1));
v___x_1014_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2));
v___x_1015_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3));
v___x_1016_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__15));
lean_inc(v_x_1002_);
v___x_1017_ = l_Lean_Syntax_isOfKind(v_x_1002_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
lean_dec(v_x_1002_);
v___x_1018_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; lean_object* v_cfgStx_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1019_ = lean_unsigned_to_nat(1u);
v_cfgStx_1020_ = l_Lean_Syntax_getArg(v_x_1002_, v___x_1019_);
v___x_1021_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfgStx_1020_);
v___x_1022_ = l_Lean_Syntax_isOfKind(v_cfgStx_1020_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; 
lean_dec(v_cfgStx_1020_);
lean_dec(v_x_1002_);
v___x_1023_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1023_;
}
else
{
lean_object* v___x_1024_; lean_object* v_tk_1025_; lean_object* v_typesStx_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1024_ = lean_unsigned_to_nat(0u);
v_tk_1025_ = l_Lean_Syntax_getArg(v_x_1002_, v___x_1024_);
v___x_1098_ = lean_unsigned_to_nat(2u);
v___x_1099_ = l_Lean_Syntax_getArg(v_x_1002_, v___x_1098_);
v___x_1100_ = l_Lean_Syntax_isNone(v___x_1099_);
if (v___x_1100_ == 0)
{
uint8_t v___x_1101_; 
lean_inc(v___x_1099_);
v___x_1101_ = l_Lean_Syntax_matchesNull(v___x_1099_, v___x_1019_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
lean_dec(v___x_1099_);
lean_dec(v_tk_1025_);
lean_dec(v_cfgStx_1020_);
lean_dec(v_x_1002_);
v___x_1102_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1102_;
}
else
{
lean_object* v_typesStx_1103_; 
v_typesStx_1103_ = l_Lean_Syntax_getArg(v___x_1099_, v___x_1024_);
lean_dec(v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_typesStx_1103_);
v___x_1107_ = l_Lean_Syntax_isOfKind(v_typesStx_1103_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; 
lean_dec(v_typesStx_1103_);
lean_dec(v_tk_1025_);
lean_dec(v_cfgStx_1020_);
lean_dec(v_x_1002_);
v___x_1108_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1108_;
}
else
{
goto v___jp_1104_;
}
}
else
{
goto v___jp_1104_;
}
v___jp_1104_:
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1105_, 0, v_typesStx_1103_);
v_typesStx_1027_ = v___x_1105_;
v___y_1028_ = v_a_1003_;
v___y_1029_ = v_a_1004_;
v___y_1030_ = v_a_1005_;
v___y_1031_ = v_a_1006_;
v___y_1032_ = v_a_1007_;
v___y_1033_ = v_a_1008_;
v___y_1034_ = v_a_1009_;
v___y_1035_ = v_a_1010_;
goto v___jp_1026_;
}
}
}
else
{
lean_object* v___x_1109_; 
lean_dec(v___x_1099_);
v___x_1109_ = lean_box(0);
v_typesStx_1027_ = v___x_1109_;
v___y_1028_ = v_a_1003_;
v___y_1029_ = v_a_1004_;
v___y_1030_ = v_a_1005_;
v___y_1031_ = v_a_1006_;
v___y_1032_ = v_a_1007_;
v___y_1033_ = v_a_1008_;
v___y_1034_ = v_a_1009_;
v___y_1035_ = v_a_1010_;
goto v___jp_1026_;
}
v___jp_1026_:
{
lean_object* v___x_1036_; lean_object* v_path_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1036_ = lean_unsigned_to_nat(3u);
v_path_1037_ = l_Lean_Syntax_getArg(v_x_1002_, v___x_1036_);
lean_dec(v_x_1002_);
v___x_1038_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__1));
lean_inc(v_path_1037_);
v___x_1039_ = l_Lean_Syntax_isOfKind(v_path_1037_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_dec(v_path_1037_);
lean_dec(v_typesStx_1027_);
lean_dec(v_tk_1025_);
lean_dec(v_cfgStx_1020_);
v___x_1040_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1096_; 
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v___x_1041_, 0);
lean_dec(v_unused_1097_);
v___x_1043_ = v___x_1041_;
v_isShared_1044_ = v_isSharedCheck_1096_;
goto v_resetjp_1042_;
}
else
{
lean_dec(v___x_1041_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1096_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1029_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v_mvarId_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v_mvarId_1047_ = lean_ctor_get(v_a_1046_, 1);
v___x_1048_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__2));
lean_inc(v_mvarId_1047_);
lean_inc(v_cfgStx_1020_);
v___x_1049_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfgStx_1020_, v_mvarId_1047_, v___x_1048_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1051_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
lean_inc(v_typesStx_1027_);
v___x_1051_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1027_, v_a_1050_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1053_ = l_Lean_TSyntax_getString(v_path_1037_);
lean_dec(v_path_1037_);
v___x_1054_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v___x_1053_, v_a_1050_, v_a_1052_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___f_1056_; lean_object* v___x_1058_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v___f_1056_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1056_, 0, v___x_1012_);
lean_closure_set(v___f_1056_, 1, v___x_1013_);
lean_closure_set(v___f_1056_, 2, v___x_1014_);
lean_closure_set(v___f_1056_, 3, v___x_1015_);
lean_closure_set(v___f_1056_, 4, v_cfgStx_1020_);
lean_closure_set(v___f_1056_, 5, v_tk_1025_);
lean_closure_set(v___f_1056_, 6, v_typesStx_1027_);
lean_closure_set(v___f_1056_, 7, v___x_1024_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 1);
lean_ctor_set(v___x_1043_, 0, v_a_1046_);
v___x_1058_ = v___x_1043_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1046_);
v___x_1058_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed), 13, 3);
lean_closure_set(v___x_1059_, 0, v___x_1058_);
lean_closure_set(v___x_1059_, 1, v_a_1055_);
lean_closure_set(v___x_1059_, 2, v___f_1056_);
v___x_1060_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1059_, v___y_1028_, v___y_1029_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_dec_ref_known(v___x_1060_, 1);
v___x_1061_ = lean_box(0);
v___x_1062_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1061_, v___y_1029_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
return v___x_1062_;
}
else
{
return v___x_1060_;
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v_a_1046_);
lean_del_object(v___x_1043_);
lean_dec(v_typesStx_1027_);
lean_dec(v_tk_1025_);
lean_dec(v_cfgStx_1020_);
v_a_1064_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1054_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1054_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec(v_a_1050_);
lean_dec(v_a_1046_);
lean_del_object(v___x_1043_);
lean_dec(v_path_1037_);
lean_dec(v_typesStx_1027_);
lean_dec(v_tk_1025_);
lean_dec(v_cfgStx_1020_);
v_a_1072_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1051_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1051_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v_a_1046_);
lean_del_object(v___x_1043_);
lean_dec(v_path_1037_);
lean_dec(v_typesStx_1027_);
lean_dec(v_tk_1025_);
lean_dec(v_cfgStx_1020_);
v_a_1080_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1049_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1049_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_del_object(v___x_1043_);
lean_dec(v_path_1037_);
lean_dec(v_typesStx_1027_);
lean_dec(v_tk_1025_);
lean_dec(v_cfgStx_1020_);
v_a_1088_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1045_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1045_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
else
{
lean_dec(v_path_1037_);
lean_dec(v_typesStx_1027_);
lean_dec(v_tk_1025_);
lean_dec(v_cfgStx_1020_);
return v___x_1041_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___boxed(lean_object* v_x_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck(v_x_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1(){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1126_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1127_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__15));
v___x_1128_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__1));
v___x_1129_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___boxed), 10, 0);
v___x_1130_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1126_, v___x_1127_, v___x_1128_, v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___boxed(lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1();
return v_res_1132_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1133_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
return v___x_1135_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1);
v___x_1137_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
lean_ctor_set(v___x_1137_, 2, v___x_1136_);
lean_ctor_set(v___x_1137_, 3, v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_unsigned_to_nat(16u);
v___x_1140_ = lean_mk_array(v___x_1139_, v___x_1138_);
return v___x_1140_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3);
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v___x_1141_);
return v___x_1143_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4);
v___x_1145_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
lean_ctor_set(v___x_1145_, 2, v___x_1144_);
lean_ctor_set(v___x_1145_, 3, v___x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0(lean_object* v___x_1148_, lean_object* v___x_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1160_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2);
v___x_1161_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5);
v___x_1162_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6));
v___x_1163_ = 0;
v___x_1164_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1164_, 0, v___x_1160_);
lean_ctor_set(v___x_1164_, 1, v___x_1161_);
lean_ctor_set(v___x_1164_, 2, v___x_1148_);
lean_ctor_set(v___x_1164_, 3, v___x_1162_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*4, v___x_1163_);
v___x_1165_ = lean_st_mk_ref(v___x_1164_);
v___x_1166_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1149_, v___x_1165_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1176_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1176_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1176_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1171_ = lean_st_ref_get(v___x_1165_);
lean_dec(v___x_1165_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v_a_1167_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1172_);
v___x_1174_ = v___x_1169_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec(v___x_1165_);
v_a_1177_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1166_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1166_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___boxed(lean_object* v___x_1185_, lean_object* v___x_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0(v___x_1185_, v___x_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___x_1186_);
return v_res_1197_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_1198_, lean_object* v_i_1199_, lean_object* v_k_1200_){
_start:
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = lean_array_get_size(v_keys_1198_);
v___x_1202_ = lean_nat_dec_lt(v_i_1199_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_dec(v_i_1199_);
return v___x_1202_;
}
else
{
lean_object* v_k_x27_1203_; uint8_t v___x_1204_; 
v_k_x27_1203_ = lean_array_fget_borrowed(v_keys_1198_, v_i_1199_);
v___x_1204_ = l_Lean_instBEqMVarId_beq(v_k_1200_, v_k_x27_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_unsigned_to_nat(1u);
v___x_1206_ = lean_nat_add(v_i_1199_, v___x_1205_);
lean_dec(v_i_1199_);
v_i_1199_ = v___x_1206_;
goto _start;
}
else
{
lean_dec(v_i_1199_);
return v___x_1202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_1208_, lean_object* v_i_1209_, lean_object* v_k_1210_){
_start:
{
uint8_t v_res_1211_; lean_object* v_r_1212_; 
v_res_1211_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1208_, v_i_1209_, v_k_1210_);
lean_dec(v_k_1210_);
lean_dec_ref(v_keys_1208_);
v_r_1212_ = lean_box(v_res_1211_);
return v_r_1212_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1213_, size_t v_x_1214_, lean_object* v_x_1215_){
_start:
{
if (lean_obj_tag(v_x_1213_) == 0)
{
lean_object* v_es_1216_; lean_object* v___x_1217_; size_t v___x_1218_; size_t v___x_1219_; lean_object* v_j_1220_; lean_object* v___x_1221_; 
v_es_1216_ = lean_ctor_get(v_x_1213_, 0);
v___x_1217_ = lean_box(2);
v___x_1218_ = ((size_t)31ULL);
v___x_1219_ = lean_usize_land(v_x_1214_, v___x_1218_);
v_j_1220_ = lean_usize_to_nat(v___x_1219_);
v___x_1221_ = lean_array_get_borrowed(v___x_1217_, v_es_1216_, v_j_1220_);
lean_dec(v_j_1220_);
switch(lean_obj_tag(v___x_1221_))
{
case 0:
{
lean_object* v_key_1222_; uint8_t v___x_1223_; 
v_key_1222_ = lean_ctor_get(v___x_1221_, 0);
v___x_1223_ = l_Lean_instBEqMVarId_beq(v_x_1215_, v_key_1222_);
return v___x_1223_;
}
case 1:
{
lean_object* v_node_1224_; size_t v___x_1225_; size_t v___x_1226_; 
v_node_1224_ = lean_ctor_get(v___x_1221_, 0);
v___x_1225_ = ((size_t)5ULL);
v___x_1226_ = lean_usize_shift_right(v_x_1214_, v___x_1225_);
v_x_1213_ = v_node_1224_;
v_x_1214_ = v___x_1226_;
goto _start;
}
default: 
{
uint8_t v___x_1228_; 
v___x_1228_ = 0;
return v___x_1228_;
}
}
}
else
{
lean_object* v_ks_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v_ks_1229_ = lean_ctor_get(v_x_1213_, 0);
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_1229_, v___x_1230_, v_x_1215_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1232_, lean_object* v_x_1233_, lean_object* v_x_1234_){
_start:
{
size_t v_x_3471__boxed_1235_; uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_x_3471__boxed_1235_ = lean_unbox_usize(v_x_1233_);
lean_dec(v_x_1233_);
v_res_1236_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1232_, v_x_3471__boxed_1235_, v_x_1234_);
lean_dec(v_x_1234_);
lean_dec_ref(v_x_1232_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(lean_object* v_x_1238_, lean_object* v_x_1239_){
_start:
{
uint64_t v___x_1240_; size_t v___x_1241_; uint8_t v___x_1242_; 
v___x_1240_ = l_Lean_instHashableMVarId_hash(v_x_1239_);
v___x_1241_ = lean_uint64_to_usize(v___x_1240_);
v___x_1242_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1238_, v___x_1241_, v_x_1239_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_1243_, lean_object* v_x_1244_){
_start:
{
uint8_t v_res_1245_; lean_object* v_r_1246_; 
v_res_1245_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_x_1243_, v_x_1244_);
lean_dec(v_x_1244_);
lean_dec_ref(v_x_1243_);
v_r_1246_ = lean_box(v_res_1245_);
return v_r_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(lean_object* v_mvarId_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v___x_1250_; lean_object* v_mctx_1251_; lean_object* v_eAssignment_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1250_ = lean_st_ref_get(v___y_1248_);
v_mctx_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc_ref(v_mctx_1251_);
lean_dec(v___x_1250_);
v_eAssignment_1252_ = lean_ctor_get(v_mctx_1251_, 8);
lean_inc_ref(v_eAssignment_1252_);
lean_dec_ref(v_mctx_1251_);
v___x_1253_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_eAssignment_1252_, v_mvarId_1247_);
lean_dec_ref(v_eAssignment_1252_);
v___x_1254_ = lean_box(v___x_1253_);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg___boxed(lean_object* v_mvarId_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v_mvarId_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec(v_mvarId_1256_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(lean_object* v_msg_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_ref_1266_; lean_object* v___x_1267_; lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1276_; 
v_ref_1266_ = lean_ctor_get(v___y_1263_, 4);
v___x_1267_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v_msg_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1270_ = v___x_1267_;
v_isShared_1271_ = v_isSharedCheck_1276_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1276_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
lean_inc(v_ref_1266_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v_ref_1266_);
lean_ctor_set(v___x_1272_, 1, v_a_1268_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 1);
lean_ctor_set(v___x_1270_, 0, v___x_1272_);
v___x_1274_ = v___x_1270_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg___boxed(lean_object* v_msg_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v_msg_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1283_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__1));
v___x_1288_ = l_Lean_stringToMessageData(v___x_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize(lean_object* v_x_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8));
lean_inc(v_x_1289_);
v___x_1300_ = l_Lean_Syntax_isOfKind(v_x_1289_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; 
lean_dec(v_x_1289_);
v___x_1301_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1301_;
}
else
{
lean_object* v___x_1302_; lean_object* v_cfg_1303_; lean_object* v_types_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1302_ = lean_unsigned_to_nat(1u);
v_cfg_1303_ = l_Lean_Syntax_getArg(v_x_1289_, v___x_1302_);
v___x_1378_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfg_1303_);
v___x_1379_ = l_Lean_Syntax_isOfKind(v_cfg_1303_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
lean_dec(v_cfg_1303_);
lean_dec(v_x_1289_);
v___x_1380_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1380_;
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1381_ = lean_unsigned_to_nat(2u);
v___x_1382_ = l_Lean_Syntax_getArg(v_x_1289_, v___x_1381_);
lean_dec(v_x_1289_);
v___x_1383_ = l_Lean_Syntax_isNone(v___x_1382_);
if (v___x_1383_ == 0)
{
uint8_t v___x_1384_; 
lean_inc(v___x_1382_);
v___x_1384_ = l_Lean_Syntax_matchesNull(v___x_1382_, v___x_1302_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; 
lean_dec(v___x_1382_);
lean_dec(v_cfg_1303_);
v___x_1385_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1385_;
}
else
{
lean_object* v___x_1386_; lean_object* v_types_1387_; 
v___x_1386_ = lean_unsigned_to_nat(0u);
v_types_1387_ = l_Lean_Syntax_getArg(v___x_1382_, v___x_1386_);
lean_dec(v___x_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_types_1387_);
v___x_1391_ = l_Lean_Syntax_isOfKind(v_types_1387_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; 
lean_dec(v_types_1387_);
lean_dec(v_cfg_1303_);
v___x_1392_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1392_;
}
else
{
goto v___jp_1388_;
}
}
else
{
goto v___jp_1388_;
}
v___jp_1388_:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_types_1387_);
v_types_1305_ = v___x_1389_;
v___y_1306_ = v_a_1290_;
v___y_1307_ = v_a_1291_;
v___y_1308_ = v_a_1292_;
v___y_1309_ = v_a_1293_;
v___y_1310_ = v_a_1294_;
v___y_1311_ = v_a_1295_;
v___y_1312_ = v_a_1296_;
v___y_1313_ = v_a_1297_;
goto v___jp_1304_;
}
}
}
else
{
lean_object* v___x_1393_; 
lean_dec(v___x_1382_);
v___x_1393_ = lean_box(0);
v_types_1305_ = v___x_1393_;
v___y_1306_ = v_a_1290_;
v___y_1307_ = v_a_1291_;
v___y_1308_ = v_a_1292_;
v___y_1309_ = v_a_1293_;
v___y_1310_ = v_a_1294_;
v___y_1311_ = v_a_1295_;
v___y_1312_ = v_a_1296_;
v___y_1313_ = v_a_1297_;
goto v___jp_1304_;
}
}
v___jp_1304_:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1312_, v___y_1313_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1376_; 
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v___x_1314_, 0);
lean_dec(v_unused_1377_);
v___x_1316_ = v___x_1314_;
v_isShared_1317_ = v_isSharedCheck_1376_;
goto v_resetjp_1315_;
}
else
{
lean_dec(v___x_1314_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1376_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1307_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v_mvarId_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v_mvarId_1320_ = lean_ctor_get(v_a_1319_, 1);
v___x_1321_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__0));
lean_inc(v_mvarId_1320_);
v___x_1322_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_1303_, v_mvarId_1320_, v___x_1321_, v___y_1312_, v___y_1313_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1324_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1322_, 1);
v___x_1324_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_1305_, v_a_1323_, v___y_1312_, v___y_1313_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v_a_1325_);
v___x_1327_ = v___x_1316_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1325_);
v___x_1327_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___f_1330_; lean_object* v___x_1331_; 
v___x_1328_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_1327_, v_a_1323_);
v___x_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1329_, 0, v_a_1319_);
v___f_1330_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1330_, 0, v___x_1329_);
lean_closure_set(v___f_1330_, 1, v___x_1328_);
v___x_1331_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_1330_, v___y_1306_, v___y_1307_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v_snd_1333_; lean_object* v_target_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v_a_1337_; uint8_t v___x_1338_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1331_, 1);
v_snd_1333_ = lean_ctor_get(v_a_1332_, 1);
lean_inc(v_snd_1333_);
lean_dec(v_a_1332_);
v_target_1334_ = lean_ctor_get(v_snd_1333_, 2);
lean_inc_ref(v_target_1334_);
lean_dec(v_snd_1333_);
v___x_1335_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1334_);
lean_dec_ref(v_target_1334_);
v___x_1336_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v___x_1335_, v___y_1311_);
lean_dec(v___x_1335_);
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref(v___x_1336_);
v___x_1338_ = lean_unbox(v_a_1337_);
lean_dec(v_a_1337_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2);
v___x_1340_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v___x_1339_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
return v___x_1340_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_box(0);
v___x_1342_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1341_, v___y_1307_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
return v___x_1342_;
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
v_a_1343_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1331_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1331_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec(v_a_1323_);
lean_dec(v_a_1319_);
lean_del_object(v___x_1316_);
v_a_1352_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1324_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1324_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_a_1319_);
lean_del_object(v___x_1316_);
lean_dec(v_types_1305_);
v_a_1360_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1322_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1322_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_del_object(v___x_1316_);
lean_dec(v_types_1305_);
lean_dec(v_cfg_1303_);
v_a_1368_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1318_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1318_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
else
{
lean_dec(v_types_1305_);
lean_dec(v_cfg_1303_);
return v___x_1314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___boxed(lean_object* v_x_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize(v_x_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0(lean_object* v_mvarId_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v_mvarId_1405_, v___y_1411_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___boxed(lean_object* v_mvarId_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0(v_mvarId_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v_mvarId_1416_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1(lean_object* v_00_u03b1_1427_, lean_object* v_msg_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v_msg_1428_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___boxed(lean_object* v_00_u03b1_1439_, lean_object* v_msg_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1(v_00_u03b1_1439_, v_msg_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
return v_res_1450_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0(lean_object* v_00_u03b2_1451_, lean_object* v_x_1452_, lean_object* v_x_1453_){
_start:
{
uint8_t v___x_1454_; 
v___x_1454_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_x_1452_, v_x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_){
_start:
{
uint8_t v_res_1458_; lean_object* v_r_1459_; 
v_res_1458_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0(v_00_u03b2_1455_, v_x_1456_, v_x_1457_);
lean_dec(v_x_1457_);
lean_dec_ref(v_x_1456_);
v_r_1459_ = lean_box(v_res_1458_);
return v_r_1459_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1460_, lean_object* v_x_1461_, size_t v_x_1462_, lean_object* v_x_1463_){
_start:
{
uint8_t v___x_1464_; 
v___x_1464_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1461_, v_x_1462_, v_x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_){
_start:
{
size_t v_x_3868__boxed_1469_; uint8_t v_res_1470_; lean_object* v_r_1471_; 
v_x_3868__boxed_1469_ = lean_unbox_usize(v_x_1467_);
lean_dec(v_x_1467_);
v_res_1470_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1(v_00_u03b2_1465_, v_x_1466_, v_x_3868__boxed_1469_, v_x_1468_);
lean_dec(v_x_1468_);
lean_dec_ref(v_x_1466_);
v_r_1471_ = lean_box(v_res_1470_);
return v_r_1471_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1472_, lean_object* v_keys_1473_, lean_object* v_vals_1474_, lean_object* v_heq_1475_, lean_object* v_i_1476_, lean_object* v_k_1477_){
_start:
{
uint8_t v___x_1478_; 
v___x_1478_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1473_, v_i_1476_, v_k_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1479_, lean_object* v_keys_1480_, lean_object* v_vals_1481_, lean_object* v_heq_1482_, lean_object* v_i_1483_, lean_object* v_k_1484_){
_start:
{
uint8_t v_res_1485_; lean_object* v_r_1486_; 
v_res_1485_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1479_, v_keys_1480_, v_vals_1481_, v_heq_1482_, v_i_1483_, v_k_1484_);
lean_dec(v_k_1484_);
lean_dec_ref(v_vals_1481_);
lean_dec_ref(v_keys_1480_);
v_r_1486_ = lean_box(v_res_1485_);
return v_r_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1(){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1492_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1493_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8));
v___x_1494_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__1));
v___x_1495_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___boxed), 10, 0);
v___x_1496_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1492_, v___x_1493_, v___x_1494_, v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___boxed(lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1();
return v_res_1498_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(lean_object* v_msg_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_4074__overap_1513_; lean_object* v___x_1514_; 
v___x_1512_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0);
v___x_4074__overap_1513_ = lean_panic_fn_borrowed(v___x_1512_, v_msg_1500_);
lean_inc(v___y_1510_);
lean_inc_ref(v___y_1509_);
lean_inc(v___y_1508_);
lean_inc_ref(v___y_1507_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1514_ = lean_apply_11(v___x_4074__overap_1513_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, lean_box(0));
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___boxed(lean_object* v_msg_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(v_msg_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec(v___y_1516_);
return v_res_1527_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__2));
v___x_1532_ = lean_unsigned_to_nat(46u);
v___x_1533_ = lean_unsigned_to_nat(98u);
v___x_1534_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__1));
v___x_1535_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__0));
v___x_1536_ = l_mkPanicMessageWithDecl(v___x_1535_, v___x_1534_, v___x_1533_, v___x_1532_, v___x_1531_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0(lean_object* v_a_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1549_ = lean_st_ref_get(v___y_1538_);
v___x_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
v___x_1551_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2);
v___x_1552_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5);
v___x_1553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6));
v___x_1554_ = 0;
v___x_1555_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1555_, 0, v___x_1551_);
lean_ctor_set(v___x_1555_, 1, v___x_1552_);
lean_ctor_set(v___x_1555_, 2, v___x_1550_);
lean_ctor_set(v___x_1555_, 3, v___x_1553_);
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*4, v___x_1554_);
v___x_1556_ = lean_st_mk_ref(v___x_1555_);
v___x_1557_ = lean_box(1);
v___x_1558_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_1557_, v_a_1537_);
v___x_1559_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1558_, v___x_1556_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec_ref(v___x_1558_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1573_; 
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v___x_1559_, 0);
lean_dec(v_unused_1574_);
v___x_1561_ = v___x_1559_;
v_isShared_1562_ = v_isSharedCheck_1573_;
goto v_resetjp_1560_;
}
else
{
lean_dec(v___x_1559_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1573_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v_target_1564_; 
v___x_1563_ = lean_st_ref_get(v___x_1556_);
lean_dec(v___x_1556_);
v_target_1564_ = lean_ctor_get(v___x_1563_, 2);
lean_inc_ref(v_target_1564_);
lean_dec(v___x_1563_);
if (lean_obj_tag(v_target_1564_) == 1)
{
lean_object* v_goal_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v_goal_1565_ = lean_ctor_get(v_target_1564_, 0);
lean_inc_ref(v_goal_1565_);
lean_dec_ref_known(v_target_1564_, 1);
v___x_1566_ = lean_st_ref_swap(v___y_1538_, v_goal_1565_);
lean_dec(v___x_1566_);
v___x_1567_ = lean_box(0);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1567_);
v___x_1569_ = v___x_1561_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec_ref(v_target_1564_);
lean_del_object(v___x_1561_);
v___x_1571_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3);
v___x_1572_ = l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(v___x_1571_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
return v___x_1572_;
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec(v___x_1556_);
v_a_1575_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1559_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1559_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___boxed(lean_object* v_a_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0(v_a_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec(v___y_1584_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(lean_object* v_x_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1));
lean_inc(v_x_1606_);
v___x_1615_ = l_Lean_Syntax_isOfKind(v_x_1606_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; 
lean_dec(v_x_1606_);
v___x_1616_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1616_;
}
else
{
lean_object* v___x_1617_; lean_object* v_cfg_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1617_ = lean_unsigned_to_nat(1u);
v_cfg_1618_ = l_Lean_Syntax_getArg(v_x_1606_, v___x_1617_);
lean_dec(v_x_1606_);
v___x_1619_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfg_1618_);
v___x_1620_ = l_Lean_Syntax_isOfKind(v_cfg_1618_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; 
lean_dec(v_cfg_1618_);
v___x_1621_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v_a_1611_, v_a_1612_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v___x_1623_; 
lean_dec_ref_known(v___x_1622_, 1);
v___x_1623_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v_mvarId_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v_mvarId_1625_ = lean_ctor_get(v_a_1624_, 1);
lean_inc(v_mvarId_1625_);
lean_dec(v_a_1624_);
v___x_1626_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__3));
v___x_1627_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_1618_, v_mvarId_1625_, v___x_1626_, v_a_1611_, v_a_1612_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___f_1629_; lean_object* v___x_1630_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1627_, 1);
v___f_1629_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1629_, 0, v_a_1628_);
v___x_1630_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___f_1629_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
return v___x_1630_;
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
v_a_1631_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1627_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1627_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v_cfg_1618_);
v_a_1639_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1623_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1623_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_dec(v_cfg_1618_);
return v___x_1622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___boxed(lean_object* v_x_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(v_x_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush(lean_object* v_x_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(v_x_1656_, v_a_1657_, v_a_1658_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___boxed(lean_object* v_x_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush(v_x_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1(){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1683_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1684_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1));
v___x_1685_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__1));
v___x_1686_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___boxed), 10, 0);
v___x_1687_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1683_, v___x_1684_, v___x_1685_, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___boxed(lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1();
return v_res_1689_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_BVDecide(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_BVDecide(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Main(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_BVDecide(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_BVDecide(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_BVDecide(builtin);
}
#ifdef __cplusplus
}
#endif
