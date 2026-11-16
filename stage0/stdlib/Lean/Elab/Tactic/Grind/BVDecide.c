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
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_create_tempfile();
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 16, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(64) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindStep"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 239, 5, 217, 230, 199, 187, 87)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grindSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "haveSilent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 40, 33, 99, 54, 221, 176, 65)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "have"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_3),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 36, 229, 233, 71, 216, 202, 183)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__13_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 99, 164, 119, 227, 118, 220, 78)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(178, 14, 254, 151, 151, 84, 196, 42)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__19_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__20_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__16_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__20_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__22_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__24_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__25_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__27_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 142, 92, 236, 193, 5, 157, 115)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 229, 98, 59, 247, 194, 34, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "bv_decide\?"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__4_value),LEAN_SCALAR_PTR_LITERAL(89, 224, 172, 67, 205, 21, 228, 63)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bvNormalize"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6_value),LEAN_SCALAR_PTR_LITERAL(42, 26, 136, 123, 235, 182, 158, 80)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value;
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvCheck"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__10_value),LEAN_SCALAR_PTR_LITERAL(39, 89, 115, 113, 62, 113, 141, 105)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bv_check"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed__const__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around."};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12_value),LEAN_SCALAR_PTR_LITERAL(150, 149, 7, 180, 70, 199, 193, 180)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value),LEAN_SCALAR_PTR_LITERAL(107, 250, 93, 18, 255, 117, 252, 211)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(lean_object* v_cfg_8_, lean_object* v_goal_9_, lean_object* v_elaborator_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_14_ = 1;
v___x_15_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___closed__0));
v___x_16_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_16_, 0, v_elaborator_10_);
lean_ctor_set_uint8(v___x_16_, sizeof(void*)*1, v___x_14_);
v___x_17_ = lean_box(0);
v___x_18_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_18_, 0, v_goal_9_);
lean_ctor_set(v___x_18_, 1, v___x_17_);
v___x_19_ = lean_st_mk_ref(v___x_18_);
v___x_20_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_8_, v___x_15_, v___x_14_, v___x_16_, v_a_11_, v_a_12_);
lean_dec_ref_known(v___x_16_, 1);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_29_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_29_ == 0)
{
v___x_23_ = v___x_20_;
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_20_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_25_; lean_object* v___x_27_; 
v___x_25_ = lean_st_ref_get(v___x_19_);
lean_dec(v___x_19_);
lean_dec(v___x_25_);
if (v_isShared_24_ == 0)
{
v___x_27_ = v___x_23_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_a_21_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
else
{
lean_dec(v___x_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___boxed(lean_object* v_cfg_30_, lean_object* v_goal_31_, lean_object* v_elaborator_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_30_, v_goal_31_, v_elaborator_32_, v_a_33_, v_a_34_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig(lean_object* v_cfg_37_, lean_object* v_goal_38_, lean_object* v_elaborator_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_37_, v_goal_38_, v_elaborator_39_, v_a_44_, v_a_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___boxed(lean_object* v_cfg_48_, lean_object* v_goal_49_, lean_object* v_elaborator_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig(v_cfg_48_, v_goal_49_, v_elaborator_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
return v_res_58_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_box(0);
v___x_60_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg(){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0);
v___x_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___boxed(lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0(lean_object* v_00_u03b1_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___boxed(lean_object* v_00_u03b1_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0(v_00_u03b1_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(lean_object* v_snd_89_, lean_object* v_ref_90_, lean_object* v_a_x3f_91_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_io_remove_file(v_snd_89_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec(v_ref_90_);
v_a_94_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_93_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_113_; 
v_a_102_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_113_ == 0)
{
v___x_104_ = v___x_93_;
v_isShared_105_ = v_isSharedCheck_113_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_93_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_113_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_106_ = lean_io_error_to_string(v_a_102_);
v___x_107_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
v___x_108_ = l_Lean_MessageData_ofFormat(v___x_107_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v_ref_90_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_109_);
v___x_111_ = v___x_104_;
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
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object* v_snd_114_, lean_object* v_ref_115_, lean_object* v_a_x3f_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_114_, v_ref_115_, v_a_x3f_116_);
lean_dec(v_a_x3f_116_);
lean_dec_ref(v_snd_114_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(lean_object* v_f_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_ref_129_; lean_object* v___x_130_; 
v_ref_129_ = lean_ctor_get(v___y_126_, 2);
v___x_130_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v_fst_132_; lean_object* v_snd_133_; lean_object* v_r_134_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref_known(v___x_130_, 1);
v_fst_132_ = lean_ctor_get(v_a_131_, 0);
lean_inc(v_fst_132_);
v_snd_133_ = lean_ctor_get(v_a_131_, 1);
lean_inc_n(v_snd_133_, 2);
lean_dec(v_a_131_);
lean_inc(v___y_127_);
lean_inc_ref(v___y_126_);
lean_inc(v___y_125_);
lean_inc_ref(v___y_124_);
lean_inc(v___y_123_);
lean_inc_ref(v___y_122_);
lean_inc(v___y_121_);
lean_inc_ref(v___y_120_);
v_r_134_ = lean_apply_11(v_f_119_, v_fst_132_, v_snd_133_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, lean_box(0));
if (lean_obj_tag(v_r_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_159_; 
v_a_135_ = lean_ctor_get(v_r_134_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v_r_134_);
if (v_isSharedCheck_159_ == 0)
{
v___x_137_ = v_r_134_;
v_isShared_138_ = v_isSharedCheck_159_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v_r_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_159_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
lean_inc(v_a_135_);
if (v_isShared_138_ == 0)
{
lean_ctor_set_tag(v___x_137_, 1);
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_158_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_141_; 
lean_inc(v_ref_129_);
v___x_141_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_133_, v_ref_129_, v___x_140_);
lean_dec_ref(v___x_140_);
lean_dec(v_snd_133_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; 
v_unused_149_ = lean_ctor_get(v___x_141_, 0);
lean_dec(v_unused_149_);
v___x_143_ = v___x_141_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_dec(v___x_141_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v_a_135_);
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_135_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
lean_dec(v_a_135_);
v_a_150_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_141_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_141_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_a_160_ = lean_ctor_get(v_r_134_, 0);
lean_inc(v_a_160_);
lean_dec_ref_known(v_r_134_, 1);
v___x_161_ = lean_box(0);
lean_inc(v_ref_129_);
v___x_162_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_133_, v_ref_129_, v___x_161_);
lean_dec(v_snd_133_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; 
v_unused_170_ = lean_ctor_get(v___x_162_, 0);
lean_dec(v_unused_170_);
v___x_164_ = v___x_162_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_dec(v___x_162_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set_tag(v___x_164_, 1);
lean_ctor_set(v___x_164_, 0, v_a_160_);
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_160_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec(v_a_160_);
v_a_171_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_162_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_162_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_190_; 
lean_dec_ref(v_f_119_);
v_a_179_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_190_ == 0)
{
v___x_181_ = v___x_130_;
v_isShared_182_ = v_isSharedCheck_190_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_130_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_190_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_183_ = lean_io_error_to_string(v_a_179_);
v___x_184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
v___x_185_ = l_Lean_MessageData_ofFormat(v___x_184_);
lean_inc(v_ref_129_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v_ref_129_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_186_);
v___x_188_ = v___x_181_;
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
lean_object* v___x_372_; lean_object* v_types_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v_types_373_ = l_Lean_Syntax_getArg(v___x_368_, v___x_372_);
lean_dec(v___x_368_);
v___x_374_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_types_373_);
v___x_375_ = l_Lean_Syntax_isOfKind(v_types_373_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_dec(v_types_373_);
lean_dec(v_cfg_318_);
v___x_376_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_376_;
}
else
{
lean_object* v___x_377_; 
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v_types_373_);
v_types_320_ = v___x_377_;
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
lean_object* v___x_378_; 
lean_dec(v___x_368_);
v___x_378_ = lean_box(0);
v_types_320_ = v___x_378_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___boxed(lean_object* v_x_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide(v_x_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1(){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_431_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_432_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5));
v___x_433_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__15));
v___x_434_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___boxed), 10, 0);
v___x_435_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_431_, v___x_432_, v___x_433_, v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___boxed(lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1();
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0(lean_object* v_x_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; 
lean_inc(v___y_442_);
lean_inc_ref(v___y_441_);
lean_inc(v___y_440_);
lean_inc_ref(v___y_439_);
v___x_448_ = lean_apply_9(v_x_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, lean_box(0));
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object* v_x_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0(v_x_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(lean_object* v_mvarId_460_, lean_object* v_x_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___f_471_; lean_object* v___x_472_; 
lean_inc(v___y_465_);
lean_inc_ref(v___y_464_);
lean_inc(v___y_463_);
lean_inc_ref(v___y_462_);
v___f_471_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_471_, 0, v_x_461_);
lean_closure_set(v___f_471_, 1, v___y_462_);
lean_closure_set(v___f_471_, 2, v___y_463_);
lean_closure_set(v___f_471_, 3, v___y_464_);
lean_closure_set(v___f_471_, 4, v___y_465_);
v___x_472_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_460_, v___f_471_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
if (lean_obj_tag(v___x_472_) == 0)
{
return v___x_472_;
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___boxed(lean_object* v_mvarId_481_, lean_object* v_x_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(v_mvarId_481_, v_x_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1(lean_object* v_00_u03b1_493_, lean_object* v_mvarId_494_, lean_object* v_x_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(v_mvarId_494_, v_x_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___boxed(lean_object* v_00_u03b1_506_, lean_object* v_mvarId_507_, lean_object* v_x_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1(v_00_u03b1_506_, v_mvarId_507_, v_x_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_518_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Array_mkArray0___redArg();
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(size_t v_sz_530_, size_t v_i_531_, lean_object* v_bs_532_, lean_object* v___y_533_){
_start:
{
uint8_t v___x_535_; 
v___x_535_ = lean_usize_dec_lt(v_i_531_, v_sz_530_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v_bs_532_);
return v___x_536_;
}
else
{
lean_object* v_ref_537_; lean_object* v_v_538_; lean_object* v___x_539_; lean_object* v_bs_x27_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; size_t v___x_548_; size_t v___x_549_; lean_object* v___x_550_; 
v_ref_537_ = lean_ctor_get(v___y_533_, 2);
v_v_538_ = lean_array_uget(v_bs_532_, v_i_531_);
v___x_539_ = lean_unsigned_to_nat(0u);
v_bs_x27_540_ = lean_array_uset(v_bs_532_, v_i_531_, v___x_539_);
v___x_541_ = 0;
v___x_542_ = l_Lean_SourceInfo_fromRef(v_ref_537_, v___x_541_);
v___x_543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1));
v___x_544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_545_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
lean_inc(v___x_542_);
v___x_546_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_546_, 0, v___x_542_);
lean_ctor_set(v___x_546_, 1, v___x_544_);
lean_ctor_set(v___x_546_, 2, v___x_545_);
v___x_547_ = l_Lean_Syntax_node2(v___x_542_, v___x_543_, v_v_538_, v___x_546_);
v___x_548_ = ((size_t)1ULL);
v___x_549_ = lean_usize_add(v_i_531_, v___x_548_);
v___x_550_ = lean_array_uset(v_bs_x27_540_, v_i_531_, v___x_547_);
v_i_531_ = v___x_549_;
v_bs_532_ = v___x_550_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___boxed(lean_object* v_sz_552_, lean_object* v_i_553_, lean_object* v_bs_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
size_t v_sz_boxed_557_; size_t v_i_boxed_558_; lean_object* v_res_559_; 
v_sz_boxed_557_ = lean_unbox_usize(v_sz_552_);
lean_dec(v_sz_552_);
v_i_boxed_558_ = lean_unbox_usize(v_i_553_);
lean_dec(v_i_553_);
v_res_559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(v_sz_boxed_557_, v_i_boxed_558_, v_bs_554_, v___y_555_);
lean_dec_ref(v___y_555_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0(lean_object* v_a_563_, size_t v___x_564_, lean_object* v___x_565_, lean_object* v___x_566_, lean_object* v___x_567_, lean_object* v___x_568_, lean_object* v_final_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; size_t v_sz_576_; lean_object* v___x_577_; 
v___x_575_ = lean_array_push(v_a_563_, v_final_569_);
v_sz_576_ = lean_array_size(v___x_575_);
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(v_sz_576_, v___x_564_, v___x_575_, v___y_572_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_600_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_600_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_600_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_600_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_ref_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v_ref_582_ = lean_ctor_get(v___y_572_, 2);
v___x_583_ = 0;
v___x_584_ = l_Lean_SourceInfo_fromRef(v_ref_582_, v___x_583_);
v___x_585_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__0));
lean_inc_ref(v___x_568_);
lean_inc_ref(v___x_567_);
lean_inc_ref(v___x_566_);
lean_inc_ref(v___x_565_);
v___x_586_ = l_Lean_Name_mkStr5(v___x_565_, v___x_566_, v___x_567_, v___x_568_, v___x_585_);
v___x_587_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__1));
v___x_588_ = l_Lean_Name_mkStr5(v___x_565_, v___x_566_, v___x_567_, v___x_568_, v___x_587_);
v___x_589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_590_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
v___x_591_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2));
v___x_592_ = l_Lean_Syntax_SepArray_ofElems(v___x_591_, v_a_578_);
lean_dec(v_a_578_);
v___x_593_ = l_Array_append___redArg(v___x_590_, v___x_592_);
lean_dec_ref(v___x_592_);
lean_inc_n(v___x_584_, 2);
v___x_594_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_594_, 0, v___x_584_);
lean_ctor_set(v___x_594_, 1, v___x_589_);
lean_ctor_set(v___x_594_, 2, v___x_593_);
v___x_595_ = l_Lean_Syntax_node1(v___x_584_, v___x_588_, v___x_594_);
v___x_596_ = l_Lean_Syntax_node1(v___x_584_, v___x_586_, v___x_595_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_596_);
v___x_598_ = v___x_580_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v___x_568_);
lean_dec_ref(v___x_567_);
lean_dec_ref(v___x_566_);
lean_dec_ref(v___x_565_);
v_a_601_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_577_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_577_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___boxed(lean_object* v_a_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v___x_613_, lean_object* v___x_614_, lean_object* v_final_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
size_t v___x_26600__boxed_621_; lean_object* v_res_622_; 
v___x_26600__boxed_621_ = lean_unbox_usize(v___x_610_);
lean_dec(v___x_610_);
v_res_622_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0(v_a_609_, v___x_26600__boxed_621_, v___x_611_, v___x_612_, v___x_613_, v___x_614_, v_final_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_622_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2));
v___x_661_ = l_String_toRawSubstring_x27(v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg(size_t v_sz_697_, size_t v_i_698_, lean_object* v_bs_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
uint8_t v___x_705_; 
v___x_705_ = lean_usize_dec_lt(v_i_698_, v_sz_697_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v_bs_699_);
return v___x_706_;
}
else
{
lean_object* v_v_707_; lean_object* v_hyp_708_; lean_object* v_grindProof_709_; lean_object* v_type_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_795_; 
v_v_707_ = lean_array_uget_borrowed(v_bs_699_, v_i_698_);
v_hyp_708_ = lean_ctor_get(v_v_707_, 0);
lean_inc_ref(v_hyp_708_);
v_grindProof_709_ = lean_ctor_get(v_v_707_, 2);
lean_inc_ref(v_grindProof_709_);
v_type_710_ = lean_ctor_get(v_hyp_708_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_hyp_708_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; lean_object* v_unused_797_; lean_object* v_unused_798_; 
v_unused_796_ = lean_ctor_get(v_hyp_708_, 3);
lean_dec(v_unused_796_);
v_unused_797_ = lean_ctor_get(v_hyp_708_, 2);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_hyp_708_, 0);
lean_dec(v_unused_798_);
v___x_712_ = v_hyp_708_;
v_isShared_713_ = v_isSharedCheck_795_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_type_710_);
lean_dec(v_hyp_708_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_795_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v_bs_x27_715_; lean_object* v_a_717_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v_bs_x27_715_ = lean_array_uset(v_bs_699_, v_i_698_, v___x_714_);
v___x_722_ = lean_box(1);
v___x_723_ = l_Lean_PrettyPrinter_delab(v_type_710_, v___x_722_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
lean_inc(v___y_703_);
lean_inc_ref(v___y_702_);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
v___x_725_ = lean_apply_5(v_grindProof_709_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, lean_box(0));
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
if (lean_obj_tag(v_a_726_) == 0)
{
lean_object* v_ref_727_; uint8_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
lean_del_object(v___x_712_);
v_ref_727_ = lean_ctor_get(v___y_702_, 2);
v___x_728_ = 0;
v___x_729_ = l_Lean_SourceInfo_fromRef(v_ref_727_, v___x_728_);
v___x_730_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1));
v___x_731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2));
lean_inc_n(v___x_729_, 3);
v___x_732_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_729_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_734_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
v___x_735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_735_, 0, v___x_729_);
lean_ctor_set(v___x_735_, 1, v___x_733_);
lean_ctor_set(v___x_735_, 2, v___x_734_);
v___x_736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__3));
v___x_737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_729_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = l_Lean_Syntax_node4(v___x_729_, v___x_730_, v___x_732_, v___x_735_, v___x_737_, v_a_724_);
v_a_717_ = v___x_738_;
goto v___jp_716_;
}
else
{
lean_object* v_toCold_739_; lean_object* v_val_740_; lean_object* v_ref_741_; lean_object* v_quotContext_742_; lean_object* v_currMacroScope_743_; uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v_toCold_739_ = lean_ctor_get(v___y_702_, 0);
v_val_740_ = lean_ctor_get(v_a_726_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v_a_726_, 1);
v_ref_741_ = lean_ctor_get(v___y_702_, 2);
v_quotContext_742_ = lean_ctor_get(v_toCold_739_, 8);
v_currMacroScope_743_ = lean_ctor_get(v_toCold_739_, 9);
v___x_744_ = 0;
v___x_745_ = l_Lean_SourceInfo_fromRef(v_ref_741_, v___x_744_);
v___x_746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2));
v___x_747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4));
lean_inc_n(v___x_745_, 2);
v___x_748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_745_);
lean_ctor_set(v___x_748_, 1, v___x_746_);
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7));
v___x_750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9));
v___x_751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11));
v___x_752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__13));
v___x_753_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14);
v___x_754_ = lean_box(0);
lean_inc(v_currMacroScope_743_);
lean_inc(v_quotContext_742_);
v___x_755_ = l_Lean_addMacroScope(v_quotContext_742_, v___x_754_, v_currMacroScope_743_);
v___x_756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__21));
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 3);
lean_ctor_set(v___x_712_, 3, v___x_756_);
lean_ctor_set(v___x_712_, 2, v___x_755_);
lean_ctor_set(v___x_712_, 1, v___x_753_);
lean_ctor_set(v___x_712_, 0, v___x_745_);
v___x_758_ = v___x_712_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v___x_756_);
v___x_758_ = v_reuseFailAlloc_778_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_inc_n(v___x_745_, 11);
v___x_759_ = l_Lean_Syntax_node1(v___x_745_, v___x_752_, v___x_758_);
v___x_760_ = l_Lean_Syntax_node1(v___x_745_, v___x_751_, v___x_759_);
v___x_761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_762_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
v___x_763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_763_, 0, v___x_745_);
lean_ctor_set(v___x_763_, 1, v___x_761_);
lean_ctor_set(v___x_763_, 2, v___x_762_);
v___x_764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23));
v___x_765_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__3));
v___x_766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_745_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = l_Lean_Syntax_node2(v___x_745_, v___x_764_, v___x_766_, v_a_724_);
v___x_768_ = l_Lean_Syntax_node1(v___x_745_, v___x_761_, v___x_767_);
v___x_769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__24));
v___x_770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_745_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26));
v___x_772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__27));
v___x_773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_745_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = l_Lean_Syntax_node2(v___x_745_, v___x_771_, v___x_773_, v_val_740_);
v___x_775_ = l_Lean_Syntax_node5(v___x_745_, v___x_750_, v___x_760_, v___x_763_, v___x_768_, v___x_770_, v___x_774_);
v___x_776_ = l_Lean_Syntax_node1(v___x_745_, v___x_749_, v___x_775_);
v___x_777_ = l_Lean_Syntax_node2(v___x_745_, v___x_747_, v___x_748_, v___x_776_);
v_a_717_ = v___x_777_;
goto v___jp_716_;
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec(v_a_724_);
lean_dec_ref(v_bs_x27_715_);
lean_del_object(v___x_712_);
v_a_779_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_725_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_725_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v_bs_x27_715_);
lean_del_object(v___x_712_);
lean_dec_ref(v_grindProof_709_);
v_a_787_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_723_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_723_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
v___jp_716_:
{
size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_add(v_i_698_, v___x_718_);
v___x_720_ = lean_array_uset(v_bs_x27_715_, v_i_698_, v_a_717_);
v_i_698_ = v___x_719_;
v_bs_699_ = v___x_720_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___boxed(lean_object* v_sz_799_, lean_object* v_i_800_, lean_object* v_bs_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
size_t v_sz_boxed_807_; size_t v_i_boxed_808_; lean_object* v_res_809_; 
v_sz_boxed_807_ = lean_unbox_usize(v_sz_799_);
lean_dec(v_sz_799_);
v_i_boxed_808_ = lean_unbox_usize(v_i_800_);
lean_dec(v_i_800_);
v_res_809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg(v_sz_boxed_807_, v_i_boxed_808_, v_bs_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0(size_t v_sz_810_, size_t v_i_811_, lean_object* v_bs_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg(v_sz_810_, v_i_811_, v_bs_812_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___boxed(lean_object* v_sz_823_, lean_object* v_i_824_, lean_object* v_bs_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
size_t v_sz_boxed_835_; size_t v_i_boxed_836_; lean_object* v_res_837_; 
v_sz_boxed_835_ = lean_unbox_usize(v_sz_823_);
lean_dec(v_sz_823_);
v_i_boxed_836_ = lean_unbox_usize(v_i_824_);
lean_dec(v_i_824_);
v_res_837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0(v_sz_boxed_835_, v_i_boxed_836_, v_bs_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace(lean_object* v_x_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_893_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0));
v___x_894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1));
v___x_895_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2));
v___x_896_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3));
v___x_897_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1));
lean_inc(v_x_875_);
v___x_898_ = l_Lean_Syntax_isOfKind(v_x_875_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
lean_dec(v_x_875_);
v___x_899_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_899_;
}
else
{
lean_object* v___x_900_; lean_object* v_cfgStx_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_900_ = lean_unsigned_to_nat(1u);
v_cfgStx_901_ = l_Lean_Syntax_getArg(v_x_875_, v___x_900_);
v___x_902_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfgStx_901_);
v___x_903_ = l_Lean_Syntax_isOfKind(v_cfgStx_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_dec(v_cfgStx_901_);
lean_dec(v_x_875_);
v___x_904_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_904_;
}
else
{
lean_object* v___x_905_; lean_object* v_tk_906_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v_typesStx_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_905_ = lean_unsigned_to_nat(0u);
v_tk_906_ = l_Lean_Syntax_getArg(v_x_875_, v___x_905_);
v___x_1152_ = lean_unsigned_to_nat(2u);
v___x_1153_ = l_Lean_Syntax_getArg(v_x_875_, v___x_1152_);
lean_dec(v_x_875_);
v___x_1154_ = l_Lean_Syntax_isNone(v___x_1153_);
if (v___x_1154_ == 0)
{
uint8_t v___x_1155_; 
lean_inc(v___x_1153_);
v___x_1155_ = l_Lean_Syntax_matchesNull(v___x_1153_, v___x_900_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
lean_dec(v___x_1153_);
lean_dec(v_tk_906_);
lean_dec(v_cfgStx_901_);
v___x_1156_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1156_;
}
else
{
lean_object* v_typesStx_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v_typesStx_1157_ = l_Lean_Syntax_getArg(v___x_1153_, v___x_905_);
lean_dec(v___x_1153_);
v___x_1158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_typesStx_1157_);
v___x_1159_ = l_Lean_Syntax_isOfKind(v_typesStx_1157_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_dec(v_typesStx_1157_);
lean_dec(v_tk_906_);
lean_dec(v_cfgStx_901_);
v___x_1160_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_typesStx_1157_);
v_typesStx_1019_ = v___x_1161_;
v___y_1020_ = v_a_876_;
v___y_1021_ = v_a_877_;
v___y_1022_ = v_a_878_;
v___y_1023_ = v_a_879_;
v___y_1024_ = v_a_880_;
v___y_1025_ = v_a_881_;
v___y_1026_ = v_a_882_;
v___y_1027_ = v_a_883_;
goto v___jp_1018_;
}
}
}
else
{
lean_object* v___x_1162_; 
lean_dec(v___x_1153_);
v___x_1162_ = lean_box(0);
v_typesStx_1019_ = v___x_1162_;
v___y_1020_ = v_a_876_;
v___y_1021_ = v_a_877_;
v___y_1022_ = v_a_878_;
v___y_1023_ = v_a_879_;
v___y_1024_ = v_a_880_;
v___y_1025_ = v_a_881_;
v___y_1026_ = v_a_882_;
v___y_1027_ = v_a_883_;
goto v___jp_1018_;
}
v___jp_907_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_inc_ref(v___y_913_);
v___x_921_ = l_Array_append___redArg(v___y_913_, v___y_920_);
lean_dec_ref(v___y_920_);
lean_inc(v___y_916_);
lean_inc(v___y_909_);
v___x_922_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_922_, 0, v___y_909_);
lean_ctor_set(v___x_922_, 1, v___y_916_);
lean_ctor_set(v___x_922_, 2, v___x_921_);
lean_inc(v___y_918_);
v___x_923_ = l_Lean_Syntax_node3(v___y_909_, v___y_918_, v___y_919_, v_cfgStx_901_, v___x_922_);
lean_inc(v___y_914_);
lean_inc_ref(v___y_910_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_911_);
v___x_924_ = lean_apply_6(v___y_915_, v___x_923_, v___y_911_, v___y_917_, v___y_910_, v___y_914_, lean_box(0));
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v___x_926_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v_a_925_);
v___x_928_ = lean_box(0);
v___x_929_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
lean_ctor_set(v___x_929_, 2, v___x_928_);
lean_ctor_set(v___x_929_, 3, v___x_928_);
lean_ctor_set(v___x_929_, 4, v___x_928_);
lean_ctor_set(v___x_929_, 5, v___x_928_);
lean_inc(v___y_912_);
v___x_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_930_, 0, v___y_912_);
v___x_931_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_932_ = 4;
v___x_933_ = l_Lean_MessageData_nil;
v___x_934_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_906_, v___x_929_, v___x_930_, v___x_931_, v___x_928_, v___x_932_, v___x_933_, v___y_910_, v___y_914_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_dec_ref_known(v___x_934_, 1);
v___y_886_ = v___y_908_;
v___y_887_ = v___y_911_;
v___y_888_ = v___y_917_;
v___y_889_ = v___y_910_;
v___y_890_ = v___y_914_;
goto v___jp_885_;
}
else
{
return v___x_934_;
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec(v_tk_906_);
v_a_935_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_924_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_924_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
v___jp_943_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
lean_inc_ref(v___y_953_);
v___x_958_ = l_Array_append___redArg(v___y_953_, v___y_957_);
lean_dec_ref(v___y_957_);
lean_inc(v___y_954_);
lean_inc(v___y_956_);
v___x_959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_959_, 0, v___y_956_);
lean_ctor_set(v___x_959_, 1, v___y_954_);
lean_ctor_set(v___x_959_, 2, v___x_958_);
v___x_960_ = lean_box(2);
v___x_961_ = l_Lean_Syntax_mkStrLit(v___y_950_, v___x_960_);
lean_inc(v___y_944_);
v___x_962_ = l_Lean_Syntax_node4(v___y_956_, v___y_944_, v___y_947_, v_cfgStx_901_, v___x_959_, v___x_961_);
lean_inc(v___y_951_);
lean_inc_ref(v___y_948_);
lean_inc(v___y_955_);
lean_inc_ref(v___y_949_);
v___x_963_ = lean_apply_6(v___y_952_, v___x_962_, v___y_949_, v___y_955_, v___y_948_, v___y_951_, lean_box(0));
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_963_, 1);
v___x_965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v_a_964_);
v___x_967_ = lean_box(0);
v___x_968_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
lean_ctor_set(v___x_968_, 2, v___x_967_);
lean_ctor_set(v___x_968_, 3, v___x_967_);
lean_ctor_set(v___x_968_, 4, v___x_967_);
lean_ctor_set(v___x_968_, 5, v___x_967_);
lean_inc(v___y_945_);
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v___y_945_);
v___x_970_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_971_ = 4;
v___x_972_ = l_Lean_MessageData_nil;
v___x_973_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_906_, v___x_968_, v___x_969_, v___x_970_, v___x_967_, v___x_971_, v___x_972_, v___y_948_, v___y_951_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_dec_ref_known(v___x_973_, 1);
v___y_886_ = v___y_946_;
v___y_887_ = v___y_949_;
v___y_888_ = v___y_955_;
v___y_889_ = v___y_948_;
v___y_890_ = v___y_951_;
goto v___jp_885_;
}
else
{
return v___x_973_;
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec(v_tk_906_);
v_a_974_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_963_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_963_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
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
v___jp_982_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
lean_inc_ref(v___y_987_);
v___x_996_ = l_Array_append___redArg(v___y_987_, v___y_995_);
lean_dec_ref(v___y_995_);
lean_inc(v___y_984_);
lean_inc(v___y_985_);
v___x_997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_997_, 0, v___y_985_);
lean_ctor_set(v___x_997_, 1, v___y_984_);
lean_ctor_set(v___x_997_, 2, v___x_996_);
lean_inc(v___y_983_);
v___x_998_ = l_Lean_Syntax_node3(v___y_985_, v___y_983_, v___y_991_, v_cfgStx_901_, v___x_997_);
lean_inc(v___y_992_);
lean_inc_ref(v___y_988_);
lean_inc(v___y_994_);
lean_inc_ref(v___y_990_);
v___x_999_ = lean_apply_6(v___y_993_, v___x_998_, v___y_990_, v___y_994_, v___y_988_, v___y_992_, lean_box(0));
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v_a_1000_);
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
lean_ctor_set(v___x_1004_, 2, v___x_1003_);
lean_ctor_set(v___x_1004_, 3, v___x_1003_);
lean_ctor_set(v___x_1004_, 4, v___x_1003_);
lean_ctor_set(v___x_1004_, 5, v___x_1003_);
lean_inc(v___y_989_);
v___x_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___y_989_);
v___x_1006_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_1007_ = 4;
v___x_1008_ = l_Lean_MessageData_nil;
v___x_1009_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_906_, v___x_1004_, v___x_1005_, v___x_1006_, v___x_1003_, v___x_1007_, v___x_1008_, v___y_988_, v___y_992_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_dec_ref_known(v___x_1009_, 1);
v___y_886_ = v___y_986_;
v___y_887_ = v___y_990_;
v___y_888_ = v___y_994_;
v___y_889_ = v___y_988_;
v___y_890_ = v___y_992_;
goto v___jp_885_;
}
else
{
return v___x_1009_;
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v_tk_906_);
v_a_1010_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_999_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_999_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
v___jp_1018_:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1150_; 
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v___x_1028_, 0);
lean_dec(v_unused_1151_);
v___x_1030_ = v___x_1028_;
v_isShared_1031_ = v_isSharedCheck_1150_;
goto v_resetjp_1029_;
}
else
{
lean_dec(v___x_1028_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1150_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1021_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v_mvarId_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v_mvarId_1034_ = lean_ctor_get(v_a_1033_, 1);
lean_inc_n(v_mvarId_1034_, 2);
v___x_1035_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__5));
lean_inc(v_cfgStx_901_);
v___x_1036_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfgStx_901_, v_mvarId_1034_, v___x_1035_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
lean_inc(v_typesStx_1019_);
v___x_1038_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1019_, v_a_1037_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1040_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_a_1037_, v_a_1039_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 1);
lean_ctor_set(v___x_1030_, 0, v_a_1033_);
v___x_1043_ = v___x_1030_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1033_);
v___x_1043_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed), 12, 2);
lean_closure_set(v___x_1044_, 0, v___x_1043_);
lean_closure_set(v___x_1044_, 1, v_a_1041_);
v___x_1045_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1044_, v___y_1020_, v___y_1021_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v_lemmas_1047_; lean_object* v_action_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1108_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v_lemmas_1047_ = lean_ctor_get(v_a_1046_, 0);
v_action_1048_ = lean_ctor_get(v_a_1046_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_a_1046_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1050_ = v_a_1046_;
v_isShared_1051_ = v_isSharedCheck_1108_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_action_1048_);
lean_inc(v_lemmas_1047_);
lean_dec(v_a_1046_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1108_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
size_t v_sz_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_sz_1052_ = lean_array_size(v_lemmas_1047_);
v___x_1053_ = lean_box_usize(v_sz_1052_);
v___x_1054_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed__const__1));
v___x_1055_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___boxed), 12, 3);
lean_closure_set(v___x_1055_, 0, v___x_1053_);
lean_closure_set(v___x_1055_, 1, v___x_1054_);
lean_closure_set(v___x_1055_, 2, v_lemmas_1047_);
v___x_1056_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(v_mvarId_1034_, v___x_1055_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1058_; lean_object* v___f_1059_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___x_1058_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed__const__1));
v___f_1059_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___boxed), 12, 6);
lean_closure_set(v___f_1059_, 0, v_a_1057_);
lean_closure_set(v___f_1059_, 1, v___x_1058_);
lean_closure_set(v___f_1059_, 2, v___x_893_);
lean_closure_set(v___f_1059_, 3, v___x_894_);
lean_closure_set(v___f_1059_, 4, v___x_895_);
lean_closure_set(v___f_1059_, 5, v___x_896_);
switch(lean_obj_tag(v_action_1048_))
{
case 0:
{
lean_object* v_ref_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v_ref_1060_ = lean_ctor_get(v___y_1026_, 2);
v___x_1061_ = 0;
v___x_1062_ = l_Lean_SourceInfo_fromRef(v_ref_1060_, v___x_1061_);
v___x_1063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7));
v___x_1064_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8));
lean_inc(v___x_1062_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set_tag(v___x_1050_, 2);
lean_ctor_set(v___x_1050_, 1, v___x_1064_);
lean_ctor_set(v___x_1050_, 0, v___x_1062_);
v___x_1066_ = v___x_1050_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1068_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1019_) == 1)
{
lean_object* v_val_1069_; lean_object* v___x_1070_; 
v_val_1069_ = lean_ctor_get(v_typesStx_1019_, 0);
lean_inc(v_val_1069_);
lean_dec_ref_known(v_typesStx_1019_, 1);
v___x_1070_ = l_Array_mkArray1___redArg(v_val_1069_);
v___y_983_ = v___x_1063_;
v___y_984_ = v___x_1067_;
v___y_985_ = v___x_1062_;
v___y_986_ = v___y_1021_;
v___y_987_ = v___x_1068_;
v___y_988_ = v___y_1026_;
v___y_989_ = v_ref_1060_;
v___y_990_ = v___y_1024_;
v___y_991_ = v___x_1066_;
v___y_992_ = v___y_1027_;
v___y_993_ = v___f_1059_;
v___y_994_ = v___y_1025_;
v___y_995_ = v___x_1070_;
goto v___jp_982_;
}
else
{
lean_object* v___x_1071_; 
lean_dec(v_typesStx_1019_);
v___x_1071_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9));
v___y_983_ = v___x_1063_;
v___y_984_ = v___x_1067_;
v___y_985_ = v___x_1062_;
v___y_986_ = v___y_1021_;
v___y_987_ = v___x_1068_;
v___y_988_ = v___y_1026_;
v___y_989_ = v_ref_1060_;
v___y_990_ = v___y_1024_;
v___y_991_ = v___x_1066_;
v___y_992_ = v___y_1027_;
v___y_993_ = v___f_1059_;
v___y_994_ = v___y_1025_;
v___y_995_ = v___x_1071_;
goto v___jp_982_;
}
}
}
case 1:
{
lean_object* v_path_1073_; lean_object* v_ref_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v_path_1073_ = lean_ctor_get(v_action_1048_, 0);
lean_inc_ref(v_path_1073_);
lean_dec_ref_known(v_action_1048_, 1);
v_ref_1074_ = lean_ctor_get(v___y_1026_, 2);
v___x_1075_ = 0;
v___x_1076_ = l_Lean_SourceInfo_fromRef(v_ref_1074_, v___x_1075_);
v___x_1077_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
v___x_1078_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12));
lean_inc(v___x_1076_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set_tag(v___x_1050_, 2);
lean_ctor_set(v___x_1050_, 1, v___x_1078_);
lean_ctor_set(v___x_1050_, 0, v___x_1076_);
v___x_1080_ = v___x_1050_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1082_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1019_) == 1)
{
lean_object* v_val_1083_; lean_object* v___x_1084_; 
v_val_1083_ = lean_ctor_get(v_typesStx_1019_, 0);
lean_inc(v_val_1083_);
lean_dec_ref_known(v_typesStx_1019_, 1);
v___x_1084_ = l_Array_mkArray1___redArg(v_val_1083_);
v___y_944_ = v___x_1077_;
v___y_945_ = v_ref_1074_;
v___y_946_ = v___y_1021_;
v___y_947_ = v___x_1080_;
v___y_948_ = v___y_1026_;
v___y_949_ = v___y_1024_;
v___y_950_ = v_path_1073_;
v___y_951_ = v___y_1027_;
v___y_952_ = v___f_1059_;
v___y_953_ = v___x_1082_;
v___y_954_ = v___x_1081_;
v___y_955_ = v___y_1025_;
v___y_956_ = v___x_1076_;
v___y_957_ = v___x_1084_;
goto v___jp_943_;
}
else
{
lean_object* v___x_1085_; 
lean_dec(v_typesStx_1019_);
v___x_1085_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9));
v___y_944_ = v___x_1077_;
v___y_945_ = v_ref_1074_;
v___y_946_ = v___y_1021_;
v___y_947_ = v___x_1080_;
v___y_948_ = v___y_1026_;
v___y_949_ = v___y_1024_;
v___y_950_ = v_path_1073_;
v___y_951_ = v___y_1027_;
v___y_952_ = v___f_1059_;
v___y_953_ = v___x_1082_;
v___y_954_ = v___x_1081_;
v___y_955_ = v___y_1025_;
v___y_956_ = v___x_1076_;
v___y_957_ = v___x_1085_;
goto v___jp_943_;
}
}
}
default: 
{
lean_object* v_ref_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v_ref_1087_ = lean_ctor_get(v___y_1026_, 2);
v___x_1088_ = 0;
v___x_1089_ = l_Lean_SourceInfo_fromRef(v_ref_1087_, v___x_1088_);
v___x_1090_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5));
v___x_1091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__6));
lean_inc(v___x_1089_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set_tag(v___x_1050_, 2);
lean_ctor_set(v___x_1050_, 1, v___x_1091_);
lean_ctor_set(v___x_1050_, 0, v___x_1089_);
v___x_1093_ = v___x_1050_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1095_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1019_) == 1)
{
lean_object* v_val_1096_; lean_object* v___x_1097_; 
v_val_1096_ = lean_ctor_get(v_typesStx_1019_, 0);
lean_inc(v_val_1096_);
lean_dec_ref_known(v_typesStx_1019_, 1);
v___x_1097_ = l_Array_mkArray1___redArg(v_val_1096_);
v___y_908_ = v___y_1021_;
v___y_909_ = v___x_1089_;
v___y_910_ = v___y_1026_;
v___y_911_ = v___y_1024_;
v___y_912_ = v_ref_1087_;
v___y_913_ = v___x_1095_;
v___y_914_ = v___y_1027_;
v___y_915_ = v___f_1059_;
v___y_916_ = v___x_1094_;
v___y_917_ = v___y_1025_;
v___y_918_ = v___x_1090_;
v___y_919_ = v___x_1093_;
v___y_920_ = v___x_1097_;
goto v___jp_907_;
}
else
{
lean_object* v___x_1098_; 
lean_dec(v_typesStx_1019_);
v___x_1098_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9));
v___y_908_ = v___y_1021_;
v___y_909_ = v___x_1089_;
v___y_910_ = v___y_1026_;
v___y_911_ = v___y_1024_;
v___y_912_ = v_ref_1087_;
v___y_913_ = v___x_1095_;
v___y_914_ = v___y_1027_;
v___y_915_ = v___f_1059_;
v___y_916_ = v___x_1094_;
v___y_917_ = v___y_1025_;
v___y_918_ = v___x_1090_;
v___y_919_ = v___x_1093_;
v___y_920_ = v___x_1098_;
goto v___jp_907_;
}
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_del_object(v___x_1050_);
lean_dec(v_action_1048_);
lean_dec(v_typesStx_1019_);
lean_dec(v_tk_906_);
lean_dec(v_cfgStx_901_);
v_a_1100_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1056_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1056_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec(v_mvarId_1034_);
lean_dec(v_typesStx_1019_);
lean_dec(v_tk_906_);
lean_dec(v_cfgStx_901_);
v_a_1109_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1045_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1045_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
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
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v_mvarId_1034_);
lean_dec(v_a_1033_);
lean_del_object(v___x_1030_);
lean_dec(v_typesStx_1019_);
lean_dec(v_tk_906_);
lean_dec(v_cfgStx_901_);
v_a_1118_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1040_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1040_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_a_1037_);
lean_dec(v_mvarId_1034_);
lean_dec(v_a_1033_);
lean_del_object(v___x_1030_);
lean_dec(v_typesStx_1019_);
lean_dec(v_tk_906_);
lean_dec(v_cfgStx_901_);
v_a_1126_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1038_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1038_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_mvarId_1034_);
lean_dec(v_a_1033_);
lean_del_object(v___x_1030_);
lean_dec(v_typesStx_1019_);
lean_dec(v_tk_906_);
lean_dec(v_cfgStx_901_);
v_a_1134_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1036_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1036_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_del_object(v___x_1030_);
lean_dec(v_typesStx_1019_);
lean_dec(v_tk_906_);
lean_dec(v_cfgStx_901_);
v_a_1142_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1032_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1032_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
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
}
else
{
lean_dec(v_typesStx_1019_);
lean_dec(v_tk_906_);
lean_dec(v_cfgStx_901_);
return v___x_1028_;
}
}
}
}
v___jp_885_:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_box(0);
v___x_892_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_891_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed(lean_object* v_x_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace(v_x_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2(size_t v_sz_1174_, size_t v_i_1175_, lean_object* v_bs_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(v_sz_1174_, v_i_1175_, v_bs_1176_, v___y_1179_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___boxed(lean_object* v_sz_1183_, lean_object* v_i_1184_, lean_object* v_bs_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
size_t v_sz_boxed_1191_; size_t v_i_boxed_1192_; lean_object* v_res_1193_; 
v_sz_boxed_1191_ = lean_unbox_usize(v_sz_1183_);
lean_dec(v_sz_1183_);
v_i_boxed_1192_ = lean_unbox_usize(v_i_1184_);
lean_dec(v_i_1184_);
v_res_1193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2(v_sz_boxed_1191_, v_i_boxed_1192_, v_bs_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1(){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1199_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1));
v___x_1201_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__1));
v___x_1202_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed), 10, 0);
v___x_1203_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1199_, v___x_1200_, v___x_1201_, v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___boxed(lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1();
return v_res_1205_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(lean_object* v_opts_1206_, lean_object* v_opt_1207_){
_start:
{
lean_object* v_name_1208_; lean_object* v_defValue_1209_; lean_object* v_map_1210_; lean_object* v___x_1211_; 
v_name_1208_ = lean_ctor_get(v_opt_1207_, 0);
v_defValue_1209_ = lean_ctor_get(v_opt_1207_, 1);
v_map_1210_ = lean_ctor_get(v_opts_1206_, 0);
v___x_1211_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1210_, v_name_1208_);
if (lean_obj_tag(v___x_1211_) == 0)
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_unbox(v_defValue_1209_);
return v___x_1212_;
}
else
{
lean_object* v_val_1213_; 
v_val_1213_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_val_1213_);
lean_dec_ref_known(v___x_1211_, 1);
if (lean_obj_tag(v_val_1213_) == 1)
{
uint8_t v_v_1214_; 
v_v_1214_ = lean_ctor_get_uint8(v_val_1213_, 0);
lean_dec_ref_known(v_val_1213_, 0);
return v_v_1214_;
}
else
{
uint8_t v___x_1215_; 
lean_dec(v_val_1213_);
v___x_1215_ = lean_unbox(v_defValue_1209_);
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_1216_, lean_object* v_opt_1217_){
_start:
{
uint8_t v_res_1218_; lean_object* v_r_1219_; 
v_res_1218_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(v_opts_1216_, v_opt_1217_);
lean_dec_ref(v_opt_1217_);
lean_dec_ref(v_opts_1216_);
v_r_1219_ = lean_box(v_res_1218_);
return v_r_1219_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_1226_, lean_object* v_x_1227_){
_start:
{
if (lean_obj_tag(v_x_1227_) == 1)
{
lean_object* v_pre_1228_; 
v_pre_1228_ = lean_ctor_get(v_x_1227_, 0);
switch(lean_obj_tag(v_pre_1228_))
{
case 1:
{
lean_object* v_pre_1229_; 
v_pre_1229_ = lean_ctor_get(v_pre_1228_, 0);
switch(lean_obj_tag(v_pre_1229_))
{
case 0:
{
lean_object* v_str_1230_; lean_object* v_str_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v_str_1230_ = lean_ctor_get(v_x_1227_, 1);
v_str_1231_ = lean_ctor_get(v_pre_1228_, 1);
v___x_1232_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3));
v___x_1233_ = lean_string_dec_eq(v_str_1231_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2));
v___x_1235_ = lean_string_dec_eq(v_str_1231_, v___x_1234_);
if (v___x_1235_ == 0)
{
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_1237_ = lean_string_dec_eq(v_str_1230_, v___x_1236_);
if (v___x_1237_ == 0)
{
return v___x_1237_;
}
else
{
return v_suppressElabErrors_1226_;
}
}
}
else
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1239_ = lean_string_dec_eq(v_str_1230_, v___x_1238_);
if (v___x_1239_ == 0)
{
return v___x_1239_;
}
else
{
return v_suppressElabErrors_1226_;
}
}
}
case 1:
{
lean_object* v_pre_1240_; 
v_pre_1240_ = lean_ctor_get(v_pre_1229_, 0);
if (lean_obj_tag(v_pre_1240_) == 0)
{
lean_object* v_str_1241_; lean_object* v_str_1242_; lean_object* v_str_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v_str_1241_ = lean_ctor_get(v_x_1227_, 1);
v_str_1242_ = lean_ctor_get(v_pre_1228_, 1);
v_str_1243_ = lean_ctor_get(v_pre_1229_, 1);
v___x_1244_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_1245_ = lean_string_dec_eq(v_str_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
return v___x_1245_;
}
else
{
lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_1247_ = lean_string_dec_eq(v_str_1242_, v___x_1246_);
if (v___x_1247_ == 0)
{
return v___x_1247_;
}
else
{
lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1248_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_1249_ = lean_string_dec_eq(v_str_1241_, v___x_1248_);
if (v___x_1249_ == 0)
{
return v___x_1249_;
}
else
{
return v_suppressElabErrors_1226_;
}
}
}
}
else
{
uint8_t v___x_1250_; 
v___x_1250_ = 0;
return v___x_1250_;
}
}
default: 
{
uint8_t v___x_1251_; 
v___x_1251_ = 0;
return v___x_1251_;
}
}
}
case 0:
{
lean_object* v_str_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v_str_1252_ = lean_ctor_get(v_x_1227_, 1);
v___x_1253_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_1254_ = lean_string_dec_eq(v_str_1252_, v___x_1253_);
if (v___x_1254_ == 0)
{
return v___x_1254_;
}
else
{
return v_suppressElabErrors_1226_;
}
}
default: 
{
uint8_t v___x_1255_; 
v___x_1255_ = 0;
return v___x_1255_;
}
}
}
else
{
uint8_t v___x_1256_; 
v___x_1256_ = 0;
return v___x_1256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1257_, lean_object* v_x_1258_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1259_; uint8_t v_res_1260_; lean_object* v_r_1261_; 
v_suppressElabErrors_boxed_1259_ = lean_unbox(v_suppressElabErrors_1257_);
v_res_1260_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_1259_, v_x_1258_);
lean_dec(v_x_1258_);
v_r_1261_ = lean_box(v_res_1260_);
return v_r_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1268_; lean_object* v_env_1269_; uint8_t v___x_1270_; lean_object* v_env_1271_; lean_object* v___x_1272_; lean_object* v_toCold_1273_; lean_object* v_mctx_1274_; lean_object* v_lctx_1275_; lean_object* v_options_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1268_ = lean_st_ref_get(v___y_1266_);
v_env_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc_ref(v_env_1269_);
lean_dec(v___x_1268_);
v___x_1270_ = 0;
v_env_1271_ = l_Lean_Environment_setRecordingDeps(v_env_1269_, v___x_1270_);
v___x_1272_ = lean_st_ref_get(v___y_1264_);
v_toCold_1273_ = lean_ctor_get(v___y_1265_, 0);
v_mctx_1274_ = lean_ctor_get(v___x_1272_, 0);
lean_inc_ref(v_mctx_1274_);
lean_dec(v___x_1272_);
v_lctx_1275_ = lean_ctor_get(v___y_1263_, 2);
v_options_1276_ = lean_ctor_get(v_toCold_1273_, 2);
lean_inc_ref(v_options_1276_);
lean_inc_ref(v_lctx_1275_);
v___x_1277_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1277_, 0, v_env_1271_);
lean_ctor_set(v___x_1277_, 1, v_mctx_1274_);
lean_ctor_set(v___x_1277_, 2, v_lctx_1275_);
lean_ctor_set(v___x_1277_, 3, v_options_1276_);
v___x_1278_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v_msgData_1262_);
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v_msgData_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(lean_object* v_ref_1287_, lean_object* v_msgData_1288_, uint8_t v_severity_1289_, uint8_t v_isSilent_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
uint8_t v___y_1297_; lean_object* v___y_1298_; uint8_t v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v_toCold_1304_; lean_object* v___y_1305_; lean_object* v___y_1334_; lean_object* v___y_1335_; uint8_t v___y_1336_; uint8_t v___y_1337_; lean_object* v___y_1338_; uint8_t v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1361_; lean_object* v___y_1362_; uint8_t v___y_1363_; uint8_t v___y_1364_; lean_object* v___y_1365_; uint8_t v___y_1366_; lean_object* v___y_1367_; uint8_t v___y_1371_; uint8_t v___y_1372_; uint8_t v___x_1382_; uint8_t v___y_1384_; uint8_t v___x_1390_; 
v___x_1382_ = 2;
v___x_1390_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1289_, v___x_1382_);
if (v___x_1390_ == 0)
{
v___y_1384_ = v___x_1390_;
goto v___jp_1383_;
}
else
{
uint8_t v___x_1391_; 
lean_inc_ref(v_msgData_1288_);
v___x_1391_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1288_);
if (v___x_1391_ == 0)
{
v___y_1384_ = v___x_1391_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec_ref(v_msgData_1288_);
v___x_1392_ = lean_box(0);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
}
v___jp_1296_:
{
lean_object* v_currNamespace_1306_; lean_object* v_openDecls_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v_env_1312_; lean_object* v_nextMacroScope_1313_; lean_object* v_ngen_1314_; lean_object* v_auxDeclNGen_1315_; lean_object* v_traceState_1316_; lean_object* v_cache_1317_; lean_object* v_recordedDeps_1318_; lean_object* v_messages_1319_; lean_object* v_infoState_1320_; lean_object* v_snapshotTasks_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1332_; 
v_currNamespace_1306_ = lean_ctor_get(v_toCold_1304_, 4);
v_openDecls_1307_ = lean_ctor_get(v_toCold_1304_, 5);
lean_inc(v_openDecls_1307_);
lean_inc(v_currNamespace_1306_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v_currNamespace_1306_);
lean_ctor_set(v___x_1308_, 1, v_openDecls_1307_);
v___x_1309_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v___y_1301_);
lean_inc_ref(v___y_1298_);
lean_inc_ref(v___y_1300_);
v___x_1310_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1310_, 0, v___y_1300_);
lean_ctor_set(v___x_1310_, 1, v___y_1303_);
lean_ctor_set(v___x_1310_, 2, v___y_1302_);
lean_ctor_set(v___x_1310_, 3, v___y_1298_);
lean_ctor_set(v___x_1310_, 4, v___x_1309_);
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*5, v___y_1297_);
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*5 + 1, v___y_1299_);
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*5 + 2, v_isSilent_1290_);
v___x_1311_ = lean_st_ref_take(v___y_1305_);
v_env_1312_ = lean_ctor_get(v___x_1311_, 0);
v_nextMacroScope_1313_ = lean_ctor_get(v___x_1311_, 1);
v_ngen_1314_ = lean_ctor_get(v___x_1311_, 2);
v_auxDeclNGen_1315_ = lean_ctor_get(v___x_1311_, 3);
v_traceState_1316_ = lean_ctor_get(v___x_1311_, 4);
v_cache_1317_ = lean_ctor_get(v___x_1311_, 5);
v_recordedDeps_1318_ = lean_ctor_get(v___x_1311_, 6);
v_messages_1319_ = lean_ctor_get(v___x_1311_, 7);
v_infoState_1320_ = lean_ctor_get(v___x_1311_, 8);
v_snapshotTasks_1321_ = lean_ctor_get(v___x_1311_, 9);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1323_ = v___x_1311_;
v_isShared_1324_ = v_isSharedCheck_1332_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_snapshotTasks_1321_);
lean_inc(v_infoState_1320_);
lean_inc(v_messages_1319_);
lean_inc(v_recordedDeps_1318_);
lean_inc(v_cache_1317_);
lean_inc(v_traceState_1316_);
lean_inc(v_auxDeclNGen_1315_);
lean_inc(v_ngen_1314_);
lean_inc(v_nextMacroScope_1313_);
lean_inc(v_env_1312_);
lean_dec(v___x_1311_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1332_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1325_ = lean_box(0);
v___x_1326_ = l_Lean_MessageLog_add(v___x_1310_, v_messages_1319_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 7, v___x_1326_);
v___x_1328_ = v___x_1323_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_env_1312_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_nextMacroScope_1313_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_ngen_1314_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v_auxDeclNGen_1315_);
lean_ctor_set(v_reuseFailAlloc_1331_, 4, v_traceState_1316_);
lean_ctor_set(v_reuseFailAlloc_1331_, 5, v_cache_1317_);
lean_ctor_set(v_reuseFailAlloc_1331_, 6, v_recordedDeps_1318_);
lean_ctor_set(v_reuseFailAlloc_1331_, 7, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1331_, 8, v_infoState_1320_);
lean_ctor_set(v_reuseFailAlloc_1331_, 9, v_snapshotTasks_1321_);
v___x_1328_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_st_ref_put(v___y_1305_, v___x_1328_);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1325_);
return v___x_1330_;
}
}
}
v___jp_1333_:
{
lean_object* v_fileName_1342_; lean_object* v_fileMap_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1359_; 
v_fileName_1342_ = lean_ctor_get(v___y_1338_, 0);
v_fileMap_1343_ = lean_ctor_get(v___y_1338_, 1);
v___x_1344_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1288_);
v___x_1345_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v___x_1344_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1359_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1359_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_inc_ref_n(v_fileMap_1343_, 2);
v___x_1350_ = l_Lean_FileMap_toPosition(v_fileMap_1343_, v___y_1340_);
lean_dec(v___y_1340_);
v___x_1351_ = l_Lean_FileMap_toPosition(v_fileMap_1343_, v___y_1341_);
lean_dec(v___y_1341_);
v___x_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
v___x_1353_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2));
if (v___y_1339_ == 0)
{
lean_del_object(v___x_1348_);
lean_dec_ref(v___y_1334_);
v___y_1297_ = v___y_1336_;
v___y_1298_ = v___x_1353_;
v___y_1299_ = v___y_1337_;
v___y_1300_ = v_fileName_1342_;
v___y_1301_ = v_a_1346_;
v___y_1302_ = v___x_1352_;
v___y_1303_ = v___x_1350_;
v_toCold_1304_ = v___y_1335_;
v___y_1305_ = v___y_1294_;
goto v___jp_1296_;
}
else
{
uint8_t v___x_1354_; 
lean_inc(v_a_1346_);
v___x_1354_ = l_Lean_MessageData_hasTag(v___y_1334_, v_a_1346_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
lean_dec_ref_known(v___x_1352_, 1);
lean_dec_ref(v___x_1350_);
lean_dec(v_a_1346_);
v___x_1355_ = lean_box(0);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1355_);
v___x_1357_ = v___x_1348_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
else
{
lean_del_object(v___x_1348_);
v___y_1297_ = v___y_1336_;
v___y_1298_ = v___x_1353_;
v___y_1299_ = v___y_1337_;
v___y_1300_ = v_fileName_1342_;
v___y_1301_ = v_a_1346_;
v___y_1302_ = v___x_1352_;
v___y_1303_ = v___x_1350_;
v_toCold_1304_ = v___y_1335_;
v___y_1305_ = v___y_1294_;
goto v___jp_1296_;
}
}
}
}
v___jp_1360_:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_Syntax_getTailPos_x3f(v___y_1365_, v___y_1364_);
lean_dec(v___y_1365_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_inc(v___y_1367_);
v___y_1334_ = v___y_1361_;
v___y_1335_ = v___y_1362_;
v___y_1336_ = v___y_1364_;
v___y_1337_ = v___y_1366_;
v___y_1338_ = v___y_1362_;
v___y_1339_ = v___y_1363_;
v___y_1340_ = v___y_1367_;
v___y_1341_ = v___y_1367_;
goto v___jp_1333_;
}
else
{
lean_object* v_val_1369_; 
v_val_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_val_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v___y_1334_ = v___y_1361_;
v___y_1335_ = v___y_1362_;
v___y_1336_ = v___y_1364_;
v___y_1337_ = v___y_1366_;
v___y_1338_ = v___y_1362_;
v___y_1339_ = v___y_1363_;
v___y_1340_ = v___y_1367_;
v___y_1341_ = v_val_1369_;
goto v___jp_1333_;
}
}
v___jp_1370_:
{
lean_object* v_toCold_1373_; lean_object* v_ref_1374_; uint8_t v_suppressElabErrors_1375_; lean_object* v___x_1376_; lean_object* v___f_1377_; lean_object* v_ref_1378_; lean_object* v___x_1379_; 
v_toCold_1373_ = lean_ctor_get(v___y_1293_, 0);
v_ref_1374_ = lean_ctor_get(v___y_1293_, 2);
v_suppressElabErrors_1375_ = lean_ctor_get_uint8(v___y_1293_, sizeof(void*)*3 + 2);
v___x_1376_ = lean_box(v_suppressElabErrors_1375_);
v___f_1377_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1377_, 0, v___x_1376_);
v_ref_1378_ = l_Lean_replaceRef(v_ref_1287_, v_ref_1374_);
v___x_1379_ = l_Lean_Syntax_getPos_x3f(v_ref_1378_, v___y_1371_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_unsigned_to_nat(0u);
v___y_1361_ = v___f_1377_;
v___y_1362_ = v_toCold_1373_;
v___y_1363_ = v_suppressElabErrors_1375_;
v___y_1364_ = v___y_1371_;
v___y_1365_ = v_ref_1378_;
v___y_1366_ = v___y_1372_;
v___y_1367_ = v___x_1380_;
goto v___jp_1360_;
}
else
{
lean_object* v_val_1381_; 
v_val_1381_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_val_1381_);
lean_dec_ref_known(v___x_1379_, 1);
v___y_1361_ = v___f_1377_;
v___y_1362_ = v_toCold_1373_;
v___y_1363_ = v_suppressElabErrors_1375_;
v___y_1364_ = v___y_1371_;
v___y_1365_ = v_ref_1378_;
v___y_1366_ = v___y_1372_;
v___y_1367_ = v_val_1381_;
goto v___jp_1360_;
}
}
v___jp_1383_:
{
uint8_t v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = 1;
v___x_1386_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1289_, v___x_1385_);
if (v___x_1386_ == 0)
{
v___y_1371_ = v___y_1384_;
v___y_1372_ = v_severity_1289_;
goto v___jp_1370_;
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1387_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1293_);
v___x_1388_ = l_Lean_warningAsError;
v___x_1389_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(v___x_1387_, v___x_1388_);
lean_dec_ref(v___x_1387_);
if (v___x_1389_ == 0)
{
v___y_1371_ = v___y_1384_;
v___y_1372_ = v_severity_1289_;
goto v___jp_1370_;
}
else
{
v___y_1371_ = v___y_1384_;
v___y_1372_ = v___x_1382_;
goto v___jp_1370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1394_, lean_object* v_msgData_1395_, lean_object* v_severity_1396_, lean_object* v_isSilent_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
uint8_t v_severity_boxed_1403_; uint8_t v_isSilent_boxed_1404_; lean_object* v_res_1405_; 
v_severity_boxed_1403_ = lean_unbox(v_severity_1396_);
v_isSilent_boxed_1404_ = lean_unbox(v_isSilent_1397_);
v_res_1405_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(v_ref_1394_, v_msgData_1395_, v_severity_boxed_1403_, v_isSilent_boxed_1404_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v_ref_1394_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(lean_object* v_msgData_1406_, uint8_t v_severity_1407_, uint8_t v_isSilent_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_ref_1414_; lean_object* v___x_1415_; 
v_ref_1414_ = lean_ctor_get(v___y_1411_, 2);
v___x_1415_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(v_ref_1414_, v_msgData_1406_, v_severity_1407_, v_isSilent_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0___boxed(lean_object* v_msgData_1416_, lean_object* v_severity_1417_, lean_object* v_isSilent_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
uint8_t v_severity_boxed_1424_; uint8_t v_isSilent_boxed_1425_; lean_object* v_res_1426_; 
v_severity_boxed_1424_ = lean_unbox(v_severity_1417_);
v_isSilent_boxed_1425_ = lean_unbox(v_isSilent_1418_);
v_res_1426_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(v_msgData_1416_, v_severity_boxed_1424_, v_isSilent_boxed_1425_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(lean_object* v_msgData_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
uint8_t v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = 1;
v___x_1434_ = 0;
v___x_1435_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(v_msgData_1427_, v___x_1433_, v___x_1434_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0___boxed(lean_object* v_msgData_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(v_msgData_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
return v_res_1442_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__2));
v___x_1448_ = l_Lean_stringToMessageData(v___x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0(lean_object* v___x_1449_, lean_object* v___x_1450_, lean_object* v___x_1451_, lean_object* v___x_1452_, lean_object* v_cfgStx_1453_, lean_object* v_tk_1454_, lean_object* v_typesStx_1455_, lean_object* v___x_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_ref_1462_; uint8_t v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___y_1473_; 
v_ref_1462_ = lean_ctor_get(v___y_1459_, 2);
v___x_1463_ = 0;
v___x_1464_ = l_Lean_SourceInfo_fromRef(v_ref_1462_, v___x_1463_);
v___x_1465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1));
v___x_1466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6));
v___x_1467_ = l_Lean_Name_mkStr5(v___x_1449_, v___x_1450_, v___x_1451_, v___x_1452_, v___x_1466_);
v___x_1468_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8));
lean_inc(v___x_1464_);
v___x_1469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1464_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1471_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1455_) == 1)
{
lean_object* v_val_1494_; lean_object* v___x_1495_; 
v_val_1494_ = lean_ctor_get(v_typesStx_1455_, 0);
lean_inc(v_val_1494_);
lean_dec_ref_known(v_typesStx_1455_, 1);
v___x_1495_ = l_Array_mkArray1___redArg(v_val_1494_);
v___y_1473_ = v___x_1495_;
goto v___jp_1472_;
}
else
{
lean_object* v___x_1496_; 
lean_dec(v_typesStx_1455_);
v___x_1496_ = lean_mk_empty_array_with_capacity(v___x_1456_);
v___y_1473_ = v___x_1496_;
goto v___jp_1472_;
}
v___jp_1472_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1474_ = l_Array_append___redArg(v___x_1471_, v___y_1473_);
lean_dec_ref(v___y_1473_);
lean_inc(v___x_1464_);
v___x_1475_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1464_);
lean_ctor_set(v___x_1475_, 1, v___x_1470_);
lean_ctor_set(v___x_1475_, 2, v___x_1474_);
v___x_1476_ = l_Lean_Syntax_node3(v___x_1464_, v___x_1467_, v___x_1469_, v_cfgStx_1453_, v___x_1475_);
v___x_1477_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3);
v___x_1478_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(v___x_1477_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1492_; 
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; 
v_unused_1493_ = lean_ctor_get(v___x_1478_, 0);
lean_dec(v_unused_1493_);
v___x_1480_ = v___x_1478_;
v_isShared_1481_ = v_isSharedCheck_1492_;
goto v_resetjp_1479_;
}
else
{
lean_dec(v___x_1478_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1492_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1465_);
lean_ctor_set(v___x_1482_, 1, v___x_1476_);
v___x_1483_ = lean_box(0);
v___x_1484_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1482_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
lean_ctor_set(v___x_1484_, 2, v___x_1483_);
lean_ctor_set(v___x_1484_, 3, v___x_1483_);
lean_ctor_set(v___x_1484_, 4, v___x_1483_);
lean_ctor_set(v___x_1484_, 5, v___x_1483_);
lean_inc(v_ref_1462_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set_tag(v___x_1480_, 1);
lean_ctor_set(v___x_1480_, 0, v_ref_1462_);
v___x_1486_ = v___x_1480_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_ref_1462_);
v___x_1486_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; uint8_t v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_1488_ = 4;
v___x_1489_ = l_Lean_MessageData_nil;
v___x_1490_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1454_, v___x_1484_, v___x_1486_, v___x_1487_, v___x_1483_, v___x_1488_, v___x_1489_, v___y_1459_, v___y_1460_);
return v___x_1490_;
}
}
}
else
{
lean_dec(v___x_1476_);
lean_dec(v_tk_1454_);
return v___x_1478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___boxed(lean_object* v___x_1497_, lean_object* v___x_1498_, lean_object* v___x_1499_, lean_object* v___x_1500_, lean_object* v_cfgStx_1501_, lean_object* v_tk_1502_, lean_object* v_typesStx_1503_, lean_object* v___x_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0(v___x_1497_, v___x_1498_, v___x_1499_, v___x_1500_, v_cfgStx_1501_, v_tk_1502_, v_typesStx_1503_, v___x_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___x_1504_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck(lean_object* v_x_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1526_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0));
v___x_1527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1));
v___x_1528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2));
v___x_1529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3));
v___x_1530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
lean_inc(v_x_1516_);
v___x_1531_ = l_Lean_Syntax_isOfKind(v_x_1516_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
lean_dec(v_x_1516_);
v___x_1532_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1532_;
}
else
{
lean_object* v___x_1533_; lean_object* v_cfgStx_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1533_ = lean_unsigned_to_nat(1u);
v_cfgStx_1534_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1533_);
v___x_1535_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfgStx_1534_);
v___x_1536_ = l_Lean_Syntax_isOfKind(v_cfgStx_1534_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
lean_dec(v_cfgStx_1534_);
lean_dec(v_x_1516_);
v___x_1537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1537_;
}
else
{
lean_object* v___x_1538_; lean_object* v_tk_1539_; lean_object* v_typesStx_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1538_ = lean_unsigned_to_nat(0u);
v_tk_1539_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1538_);
v___x_1612_ = lean_unsigned_to_nat(2u);
v___x_1613_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1612_);
v___x_1614_ = l_Lean_Syntax_isNone(v___x_1613_);
if (v___x_1614_ == 0)
{
uint8_t v___x_1615_; 
lean_inc(v___x_1613_);
v___x_1615_ = l_Lean_Syntax_matchesNull(v___x_1613_, v___x_1533_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; 
lean_dec(v___x_1613_);
lean_dec(v_tk_1539_);
lean_dec(v_cfgStx_1534_);
lean_dec(v_x_1516_);
v___x_1616_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1616_;
}
else
{
lean_object* v_typesStx_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v_typesStx_1617_ = l_Lean_Syntax_getArg(v___x_1613_, v___x_1538_);
lean_dec(v___x_1613_);
v___x_1618_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_typesStx_1617_);
v___x_1619_ = l_Lean_Syntax_isOfKind(v_typesStx_1617_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
lean_dec(v_typesStx_1617_);
lean_dec(v_tk_1539_);
lean_dec(v_cfgStx_1534_);
lean_dec(v_x_1516_);
v___x_1620_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1620_;
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1621_, 0, v_typesStx_1617_);
v_typesStx_1541_ = v___x_1621_;
v___y_1542_ = v_a_1517_;
v___y_1543_ = v_a_1518_;
v___y_1544_ = v_a_1519_;
v___y_1545_ = v_a_1520_;
v___y_1546_ = v_a_1521_;
v___y_1547_ = v_a_1522_;
v___y_1548_ = v_a_1523_;
v___y_1549_ = v_a_1524_;
goto v___jp_1540_;
}
}
}
else
{
lean_object* v___x_1622_; 
lean_dec(v___x_1613_);
v___x_1622_ = lean_box(0);
v_typesStx_1541_ = v___x_1622_;
v___y_1542_ = v_a_1517_;
v___y_1543_ = v_a_1518_;
v___y_1544_ = v_a_1519_;
v___y_1545_ = v_a_1520_;
v___y_1546_ = v_a_1521_;
v___y_1547_ = v_a_1522_;
v___y_1548_ = v_a_1523_;
v___y_1549_ = v_a_1524_;
goto v___jp_1540_;
}
v___jp_1540_:
{
lean_object* v___x_1550_; lean_object* v_path_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1550_ = lean_unsigned_to_nat(3u);
v_path_1551_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1550_);
lean_dec(v_x_1516_);
v___x_1552_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__1));
lean_inc(v_path_1551_);
v___x_1553_ = l_Lean_Syntax_isOfKind(v_path_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_dec(v_path_1551_);
lean_dec(v_typesStx_1541_);
lean_dec(v_tk_1539_);
lean_dec(v_cfgStx_1534_);
v___x_1554_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1554_;
}
else
{
lean_object* v___f_1555_; lean_object* v___x_1556_; 
lean_inc(v_typesStx_1541_);
lean_inc(v_cfgStx_1534_);
v___f_1555_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1555_, 0, v___x_1526_);
lean_closure_set(v___f_1555_, 1, v___x_1527_);
lean_closure_set(v___f_1555_, 2, v___x_1528_);
lean_closure_set(v___f_1555_, 3, v___x_1529_);
lean_closure_set(v___f_1555_, 4, v_cfgStx_1534_);
lean_closure_set(v___f_1555_, 5, v_tk_1539_);
lean_closure_set(v___f_1555_, 6, v_typesStx_1541_);
lean_closure_set(v___f_1555_, 7, v___x_1538_);
v___x_1556_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1610_; 
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; 
v_unused_1611_ = lean_ctor_get(v___x_1556_, 0);
lean_dec(v_unused_1611_);
v___x_1558_ = v___x_1556_;
v_isShared_1559_ = v_isSharedCheck_1610_;
goto v_resetjp_1557_;
}
else
{
lean_dec(v___x_1556_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1610_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1543_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v_mvarId_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v_mvarId_1562_ = lean_ctor_get(v_a_1561_, 1);
v___x_1563_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__2));
lean_inc(v_mvarId_1562_);
v___x_1564_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfgStx_1534_, v_mvarId_1562_, v___x_1563_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1566_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v___x_1566_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1541_, v_a_1565_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1566_, 1);
v___x_1568_ = l_Lean_TSyntax_getString(v_path_1551_);
lean_dec(v_path_1551_);
v___x_1569_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v___x_1568_, v_a_1565_, v_a_1567_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
if (v_isShared_1559_ == 0)
{
lean_ctor_set_tag(v___x_1558_, 1);
lean_ctor_set(v___x_1558_, 0, v_a_1561_);
v___x_1572_ = v___x_1558_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1561_);
v___x_1572_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed), 13, 3);
lean_closure_set(v___x_1573_, 0, v___x_1572_);
lean_closure_set(v___x_1573_, 1, v_a_1570_);
lean_closure_set(v___x_1573_, 2, v___f_1555_);
v___x_1574_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1573_, v___y_1542_, v___y_1543_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_dec_ref_known(v___x_1574_, 1);
v___x_1575_ = lean_box(0);
v___x_1576_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1575_, v___y_1543_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
return v___x_1576_;
}
else
{
return v___x_1574_;
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec(v_a_1561_);
lean_del_object(v___x_1558_);
lean_dec_ref(v___f_1555_);
v_a_1578_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1569_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1569_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec(v_a_1565_);
lean_dec(v_a_1561_);
lean_del_object(v___x_1558_);
lean_dec_ref(v___f_1555_);
lean_dec(v_path_1551_);
v_a_1586_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1566_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1566_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v_a_1561_);
lean_del_object(v___x_1558_);
lean_dec_ref(v___f_1555_);
lean_dec(v_path_1551_);
lean_dec(v_typesStx_1541_);
v_a_1594_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1564_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1564_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_del_object(v___x_1558_);
lean_dec_ref(v___f_1555_);
lean_dec(v_path_1551_);
lean_dec(v_typesStx_1541_);
lean_dec(v_cfgStx_1534_);
v_a_1602_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1560_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1560_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
else
{
lean_dec_ref(v___f_1555_);
lean_dec(v_path_1551_);
lean_dec(v_typesStx_1541_);
lean_dec(v_cfgStx_1534_);
return v___x_1556_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___boxed(lean_object* v_x_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck(v_x_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1(){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1639_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
v___x_1641_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__1));
v___x_1642_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___boxed), 10, 0);
v___x_1643_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1639_, v___x_1640_, v___x_1641_, v___x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___boxed(lean_object* v_a_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1();
return v_res_1645_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1646_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
return v___x_1648_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1);
v___x_1650_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
lean_ctor_set(v___x_1650_, 2, v___x_1649_);
lean_ctor_set(v___x_1650_, 3, v___x_1649_);
return v___x_1650_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1651_ = lean_box(0);
v___x_1652_ = lean_unsigned_to_nat(16u);
v___x_1653_ = lean_mk_array(v___x_1652_, v___x_1651_);
return v___x_1653_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3);
v___x_1655_ = lean_unsigned_to_nat(0u);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v___x_1654_);
return v___x_1656_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4);
v___x_1658_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
lean_ctor_set(v___x_1658_, 2, v___x_1657_);
lean_ctor_set(v___x_1658_, 3, v___x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0(lean_object* v___x_1661_, lean_object* v___x_1662_, lean_object* v___x_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1674_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2);
v___x_1675_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5);
v___x_1676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6));
v___x_1677_ = 0;
v___x_1678_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1678_, 0, v___x_1674_);
lean_ctor_set(v___x_1678_, 1, v___x_1675_);
lean_ctor_set(v___x_1678_, 2, v___x_1661_);
lean_ctor_set(v___x_1678_, 3, v___x_1676_);
lean_ctor_set_uint8(v___x_1678_, sizeof(void*)*4, v___x_1677_);
v___x_1679_ = lean_st_mk_ref(v___x_1678_);
v___x_1680_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1662_, v___x_1663_, v___x_1679_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1690_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1690_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1690_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1685_ = lean_st_ref_get(v___x_1679_);
lean_dec(v___x_1679_);
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_a_1681_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1686_);
v___x_1688_ = v___x_1683_;
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
lean_dec(v___x_1679_);
v_a_1691_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1680_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1680_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___boxed(lean_object* v___x_1699_, lean_object* v___x_1700_, lean_object* v___x_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0(v___x_1699_, v___x_1700_, v___x_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___x_1701_);
lean_dec(v___x_1700_);
return v_res_1712_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_1713_, lean_object* v_i_1714_, lean_object* v_k_1715_){
_start:
{
lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1716_ = lean_array_get_size(v_keys_1713_);
v___x_1717_ = lean_nat_dec_lt(v_i_1714_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_dec(v_i_1714_);
return v___x_1717_;
}
else
{
lean_object* v_k_x27_1718_; uint8_t v___x_1719_; 
v_k_x27_1718_ = lean_array_fget_borrowed(v_keys_1713_, v_i_1714_);
v___x_1719_ = l_Lean_instBEqMVarId_beq(v_k_1715_, v_k_x27_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = lean_unsigned_to_nat(1u);
v___x_1721_ = lean_nat_add(v_i_1714_, v___x_1720_);
lean_dec(v_i_1714_);
v_i_1714_ = v___x_1721_;
goto _start;
}
else
{
lean_dec(v_i_1714_);
return v___x_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_1723_, lean_object* v_i_1724_, lean_object* v_k_1725_){
_start:
{
uint8_t v_res_1726_; lean_object* v_r_1727_; 
v_res_1726_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1723_, v_i_1724_, v_k_1725_);
lean_dec(v_k_1725_);
lean_dec_ref(v_keys_1723_);
v_r_1727_ = lean_box(v_res_1726_);
return v_r_1727_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1728_, size_t v_x_1729_, lean_object* v_x_1730_){
_start:
{
if (lean_obj_tag(v_x_1728_) == 0)
{
lean_object* v_es_1731_; lean_object* v___x_1732_; size_t v___x_1733_; size_t v___x_1734_; lean_object* v_j_1735_; lean_object* v___x_1736_; 
v_es_1731_ = lean_ctor_get(v_x_1728_, 0);
v___x_1732_ = lean_box(2);
v___x_1733_ = ((size_t)31ULL);
v___x_1734_ = lean_usize_land(v_x_1729_, v___x_1733_);
v_j_1735_ = lean_usize_to_nat(v___x_1734_);
v___x_1736_ = lean_array_get_borrowed(v___x_1732_, v_es_1731_, v_j_1735_);
lean_dec(v_j_1735_);
switch(lean_obj_tag(v___x_1736_))
{
case 0:
{
lean_object* v_key_1737_; uint8_t v___x_1738_; 
v_key_1737_ = lean_ctor_get(v___x_1736_, 0);
v___x_1738_ = l_Lean_instBEqMVarId_beq(v_x_1730_, v_key_1737_);
return v___x_1738_;
}
case 1:
{
lean_object* v_node_1739_; size_t v___x_1740_; size_t v___x_1741_; 
v_node_1739_ = lean_ctor_get(v___x_1736_, 0);
v___x_1740_ = ((size_t)5ULL);
v___x_1741_ = lean_usize_shift_right(v_x_1729_, v___x_1740_);
v_x_1728_ = v_node_1739_;
v_x_1729_ = v___x_1741_;
goto _start;
}
default: 
{
uint8_t v___x_1743_; 
v___x_1743_ = 0;
return v___x_1743_;
}
}
}
else
{
lean_object* v_ks_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v_ks_1744_ = lean_ctor_get(v_x_1728_, 0);
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_1744_, v___x_1745_, v_x_1730_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_){
_start:
{
size_t v_x_3473__boxed_1750_; uint8_t v_res_1751_; lean_object* v_r_1752_; 
v_x_3473__boxed_1750_ = lean_unbox_usize(v_x_1748_);
lean_dec(v_x_1748_);
v_res_1751_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1747_, v_x_3473__boxed_1750_, v_x_1749_);
lean_dec(v_x_1749_);
lean_dec_ref(v_x_1747_);
v_r_1752_ = lean_box(v_res_1751_);
return v_r_1752_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(lean_object* v_x_1753_, lean_object* v_x_1754_){
_start:
{
uint64_t v___x_1755_; size_t v___x_1756_; uint8_t v___x_1757_; 
v___x_1755_ = l_Lean_instHashableMVarId_hash(v_x_1754_);
v___x_1756_ = lean_uint64_to_usize(v___x_1755_);
v___x_1757_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1753_, v___x_1756_, v_x_1754_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_1758_, lean_object* v_x_1759_){
_start:
{
uint8_t v_res_1760_; lean_object* v_r_1761_; 
v_res_1760_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_x_1758_, v_x_1759_);
lean_dec(v_x_1759_);
lean_dec_ref(v_x_1758_);
v_r_1761_ = lean_box(v_res_1760_);
return v_r_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(lean_object* v_mvarId_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; lean_object* v_mctx_1766_; lean_object* v_eAssignment_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1765_ = lean_st_ref_get(v___y_1763_);
v_mctx_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc_ref(v_mctx_1766_);
lean_dec(v___x_1765_);
v_eAssignment_1767_ = lean_ctor_get(v_mctx_1766_, 8);
lean_inc_ref(v_eAssignment_1767_);
lean_dec_ref(v_mctx_1766_);
v___x_1768_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_eAssignment_1767_, v_mvarId_1762_);
lean_dec_ref(v_eAssignment_1767_);
v___x_1769_ = lean_box(v___x_1768_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg___boxed(lean_object* v_mvarId_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v_mvarId_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec(v_mvarId_1771_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(lean_object* v_msg_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_ref_1781_; lean_object* v___x_1782_; lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1791_; 
v_ref_1781_ = lean_ctor_get(v___y_1778_, 2);
v___x_1782_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v_msg_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1791_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1791_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v___x_1789_; 
lean_inc(v_ref_1781_);
v___x_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1787_, 0, v_ref_1781_);
lean_ctor_set(v___x_1787_, 1, v_a_1783_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set_tag(v___x_1785_, 1);
lean_ctor_set(v___x_1785_, 0, v___x_1787_);
v___x_1789_ = v___x_1785_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg___boxed(lean_object* v_msg_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v_msg_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
return v_res_1798_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__1));
v___x_1803_ = l_Lean_stringToMessageData(v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize(lean_object* v_x_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7));
lean_inc(v_x_1804_);
v___x_1815_ = l_Lean_Syntax_isOfKind(v_x_1804_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; 
lean_dec(v_x_1804_);
v___x_1816_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1816_;
}
else
{
lean_object* v___x_1817_; lean_object* v_cfg_1818_; lean_object* v_types_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1817_ = lean_unsigned_to_nat(1u);
v_cfg_1818_ = l_Lean_Syntax_getArg(v_x_1804_, v___x_1817_);
v___x_1894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfg_1818_);
v___x_1895_ = l_Lean_Syntax_isOfKind(v_cfg_1818_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; 
lean_dec(v_cfg_1818_);
lean_dec(v_x_1804_);
v___x_1896_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1897_ = lean_unsigned_to_nat(2u);
v___x_1898_ = l_Lean_Syntax_getArg(v_x_1804_, v___x_1897_);
lean_dec(v_x_1804_);
v___x_1899_ = l_Lean_Syntax_isNone(v___x_1898_);
if (v___x_1899_ == 0)
{
uint8_t v___x_1900_; 
lean_inc(v___x_1898_);
v___x_1900_ = l_Lean_Syntax_matchesNull(v___x_1898_, v___x_1817_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; 
lean_dec(v___x_1898_);
lean_dec(v_cfg_1818_);
v___x_1901_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1901_;
}
else
{
lean_object* v___x_1902_; lean_object* v_types_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1902_ = lean_unsigned_to_nat(0u);
v_types_1903_ = l_Lean_Syntax_getArg(v___x_1898_, v___x_1902_);
lean_dec(v___x_1898_);
v___x_1904_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_types_1903_);
v___x_1905_ = l_Lean_Syntax_isOfKind(v_types_1903_, v___x_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; 
lean_dec(v_types_1903_);
lean_dec(v_cfg_1818_);
v___x_1906_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1906_;
}
else
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1907_, 0, v_types_1903_);
v_types_1820_ = v___x_1907_;
v___y_1821_ = v_a_1805_;
v___y_1822_ = v_a_1806_;
v___y_1823_ = v_a_1807_;
v___y_1824_ = v_a_1808_;
v___y_1825_ = v_a_1809_;
v___y_1826_ = v_a_1810_;
v___y_1827_ = v_a_1811_;
v___y_1828_ = v_a_1812_;
goto v___jp_1819_;
}
}
}
else
{
lean_object* v___x_1908_; 
lean_dec(v___x_1898_);
v___x_1908_ = lean_box(0);
v_types_1820_ = v___x_1908_;
v___y_1821_ = v_a_1805_;
v___y_1822_ = v_a_1806_;
v___y_1823_ = v_a_1807_;
v___y_1824_ = v_a_1808_;
v___y_1825_ = v_a_1809_;
v___y_1826_ = v_a_1810_;
v___y_1827_ = v_a_1811_;
v___y_1828_ = v_a_1812_;
goto v___jp_1819_;
}
}
v___jp_1819_:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1892_; 
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1892_ == 0)
{
lean_object* v_unused_1893_; 
v_unused_1893_ = lean_ctor_get(v___x_1829_, 0);
lean_dec(v_unused_1893_);
v___x_1831_ = v___x_1829_;
v_isShared_1832_ = v_isSharedCheck_1892_;
goto v_resetjp_1830_;
}
else
{
lean_dec(v___x_1829_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1892_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1822_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v_mvarId_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v_mvarId_1835_ = lean_ctor_get(v_a_1834_, 1);
v___x_1836_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__0));
lean_inc(v_mvarId_1835_);
v___x_1837_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_1818_, v_mvarId_1835_, v___x_1836_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1839_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref_known(v___x_1837_, 1);
v___x_1839_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_1820_, v_a_1838_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v___x_1839_, 1);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v_a_1840_);
v___x_1842_ = v___x_1831_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1840_);
v___x_1842_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___f_1846_; lean_object* v___x_1847_; 
v___x_1843_ = lean_box(0);
v___x_1844_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_1842_, v_a_1838_, v___x_1843_);
v___x_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1845_, 0, v_a_1834_);
v___f_1846_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___boxed), 13, 3);
lean_closure_set(v___f_1846_, 0, v___x_1845_);
lean_closure_set(v___f_1846_, 1, v___x_1843_);
lean_closure_set(v___f_1846_, 2, v___x_1844_);
v___x_1847_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_1846_, v___y_1821_, v___y_1822_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v_snd_1849_; lean_object* v_target_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v_a_1853_; uint8_t v___x_1854_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1847_, 1);
v_snd_1849_ = lean_ctor_get(v_a_1848_, 1);
lean_inc(v_snd_1849_);
lean_dec(v_a_1848_);
v_target_1850_ = lean_ctor_get(v_snd_1849_, 2);
lean_inc_ref(v_target_1850_);
lean_dec(v_snd_1849_);
v___x_1851_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1850_);
lean_dec_ref(v_target_1850_);
v___x_1852_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v___x_1851_, v___y_1826_);
lean_dec(v___x_1851_);
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref(v___x_1852_);
v___x_1854_ = lean_unbox(v_a_1853_);
lean_dec(v_a_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2);
v___x_1856_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v___x_1855_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_box(0);
v___x_1858_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1857_, v___y_1822_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
return v___x_1858_;
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
v_a_1859_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1847_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1847_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec(v_a_1838_);
lean_dec(v_a_1834_);
lean_del_object(v___x_1831_);
v_a_1868_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1839_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1839_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec(v_a_1834_);
lean_del_object(v___x_1831_);
lean_dec(v_types_1820_);
v_a_1876_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1837_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1837_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_del_object(v___x_1831_);
lean_dec(v_types_1820_);
lean_dec(v_cfg_1818_);
v_a_1884_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1833_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1833_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
else
{
lean_dec(v_types_1820_);
lean_dec(v_cfg_1818_);
return v___x_1829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___boxed(lean_object* v_x_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize(v_x_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
lean_dec(v_a_1913_);
lean_dec_ref(v_a_1912_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0(lean_object* v_mvarId_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v_mvarId_1920_, v___y_1926_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___boxed(lean_object* v_mvarId_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0(v_mvarId_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v_mvarId_1931_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1(lean_object* v_00_u03b1_1942_, lean_object* v_msg_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v_msg_1943_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___boxed(lean_object* v_00_u03b1_1954_, lean_object* v_msg_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1(v_00_u03b1_1954_, v_msg_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
return v_res_1965_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0(lean_object* v_00_u03b2_1966_, lean_object* v_x_1967_, lean_object* v_x_1968_){
_start:
{
uint8_t v___x_1969_; 
v___x_1969_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_x_1967_, v_x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1970_, lean_object* v_x_1971_, lean_object* v_x_1972_){
_start:
{
uint8_t v_res_1973_; lean_object* v_r_1974_; 
v_res_1973_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0(v_00_u03b2_1970_, v_x_1971_, v_x_1972_);
lean_dec(v_x_1972_);
lean_dec_ref(v_x_1971_);
v_r_1974_ = lean_box(v_res_1973_);
return v_r_1974_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1975_, lean_object* v_x_1976_, size_t v_x_1977_, lean_object* v_x_1978_){
_start:
{
uint8_t v___x_1979_; 
v___x_1979_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1976_, v_x_1977_, v_x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1980_, lean_object* v_x_1981_, lean_object* v_x_1982_, lean_object* v_x_1983_){
_start:
{
size_t v_x_3870__boxed_1984_; uint8_t v_res_1985_; lean_object* v_r_1986_; 
v_x_3870__boxed_1984_ = lean_unbox_usize(v_x_1982_);
lean_dec(v_x_1982_);
v_res_1985_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1(v_00_u03b2_1980_, v_x_1981_, v_x_3870__boxed_1984_, v_x_1983_);
lean_dec(v_x_1983_);
lean_dec_ref(v_x_1981_);
v_r_1986_ = lean_box(v_res_1985_);
return v_r_1986_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1987_, lean_object* v_keys_1988_, lean_object* v_vals_1989_, lean_object* v_heq_1990_, lean_object* v_i_1991_, lean_object* v_k_1992_){
_start:
{
uint8_t v___x_1993_; 
v___x_1993_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1988_, v_i_1991_, v_k_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1994_, lean_object* v_keys_1995_, lean_object* v_vals_1996_, lean_object* v_heq_1997_, lean_object* v_i_1998_, lean_object* v_k_1999_){
_start:
{
uint8_t v_res_2000_; lean_object* v_r_2001_; 
v_res_2000_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1994_, v_keys_1995_, v_vals_1996_, v_heq_1997_, v_i_1998_, v_k_1999_);
lean_dec(v_k_1999_);
lean_dec_ref(v_vals_1996_);
lean_dec_ref(v_keys_1995_);
v_r_2001_ = lean_box(v_res_2000_);
return v_r_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1(){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2007_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2008_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7));
v___x_2009_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__1));
v___x_2010_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___boxed), 10, 0);
v___x_2011_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2007_, v___x_2008_, v___x_2009_, v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___boxed(lean_object* v_a_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1();
return v_res_2013_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(lean_object* v_msg_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_4094__overap_2028_; lean_object* v___x_2029_; 
v___x_2027_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0);
v___x_4094__overap_2028_ = lean_panic_fn_borrowed(v___x_2027_, v_msg_2015_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
lean_inc(v___y_2021_);
lean_inc_ref(v___y_2020_);
lean_inc(v___y_2019_);
lean_inc_ref(v___y_2018_);
lean_inc(v___y_2017_);
lean_inc(v___y_2016_);
v___x_2029_ = lean_apply_11(v___x_4094__overap_2028_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, lean_box(0));
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___boxed(lean_object* v_msg_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(v_msg_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec(v___y_2031_);
return v_res_2042_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2046_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__2));
v___x_2047_ = lean_unsigned_to_nat(46u);
v___x_2048_ = lean_unsigned_to_nat(113u);
v___x_2049_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__1));
v___x_2050_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__0));
v___x_2051_ = l_mkPanicMessageWithDecl(v___x_2050_, v___x_2049_, v___x_2048_, v___x_2047_, v___x_2046_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0(lean_object* v_a_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2064_ = lean_st_ref_get(v___y_2053_);
v___x_2065_ = lean_box(1);
v___x_2066_ = lean_box(0);
v___x_2067_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_2065_, v_a_2052_, v___x_2066_);
v___x_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2064_);
v___x_2069_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2);
v___x_2070_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5);
v___x_2071_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6));
v___x_2072_ = 0;
v___x_2073_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2073_, 0, v___x_2069_);
lean_ctor_set(v___x_2073_, 1, v___x_2070_);
lean_ctor_set(v___x_2073_, 2, v___x_2068_);
lean_ctor_set(v___x_2073_, 3, v___x_2071_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*4, v___x_2072_);
v___x_2074_ = lean_st_mk_ref(v___x_2073_);
v___x_2075_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_2066_, v___x_2067_, v___x_2074_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec_ref(v___x_2067_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2089_; 
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2089_ == 0)
{
lean_object* v_unused_2090_; 
v_unused_2090_ = lean_ctor_get(v___x_2075_, 0);
lean_dec(v_unused_2090_);
v___x_2077_ = v___x_2075_;
v_isShared_2078_ = v_isSharedCheck_2089_;
goto v_resetjp_2076_;
}
else
{
lean_dec(v___x_2075_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2089_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v_target_2080_; 
v___x_2079_ = lean_st_ref_get(v___x_2074_);
lean_dec(v___x_2074_);
v_target_2080_ = lean_ctor_get(v___x_2079_, 2);
lean_inc_ref(v_target_2080_);
lean_dec(v___x_2079_);
if (lean_obj_tag(v_target_2080_) == 1)
{
lean_object* v_goal_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
v_goal_2081_ = lean_ctor_get(v_target_2080_, 0);
lean_inc_ref(v_goal_2081_);
lean_dec_ref_known(v_target_2080_, 1);
v___x_2082_ = lean_box(0);
v___x_2083_ = lean_st_ref_swap(v___y_2053_, v_goal_2081_);
lean_dec(v___x_2083_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2082_);
v___x_2085_ = v___x_2077_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2082_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec_ref(v_target_2080_);
lean_del_object(v___x_2077_);
v___x_2087_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3);
v___x_2088_ = l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(v___x_2087_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
return v___x_2088_;
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v___x_2074_);
v_a_2091_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2075_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2075_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___boxed(lean_object* v_a_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0(v_a_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec(v___y_2100_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(lean_object* v_x_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2130_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1));
lean_inc(v_x_2122_);
v___x_2131_ = l_Lean_Syntax_isOfKind(v_x_2122_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; 
lean_dec(v_x_2122_);
v___x_2132_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_2132_;
}
else
{
lean_object* v___x_2133_; lean_object* v_cfg_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2133_ = lean_unsigned_to_nat(1u);
v_cfg_2134_ = l_Lean_Syntax_getArg(v_x_2122_, v___x_2133_);
lean_dec(v_x_2122_);
v___x_2135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfg_2134_);
v___x_2136_ = l_Lean_Syntax_isOfKind(v_cfg_2134_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; 
lean_dec(v_cfg_2134_);
v___x_2137_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_2137_;
}
else
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v_a_2127_, v_a_2128_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v___x_2139_; 
lean_dec_ref_known(v___x_2138_, 1);
v___x_2139_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v_mvarId_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v_mvarId_2141_ = lean_ctor_get(v_a_2140_, 1);
lean_inc(v_mvarId_2141_);
lean_dec(v_a_2140_);
v___x_2142_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__3));
v___x_2143_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_2134_, v_mvarId_2141_, v___x_2142_, v_a_2127_, v_a_2128_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___f_2145_; lean_object* v___x_2146_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v___f_2145_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2145_, 0, v_a_2144_);
v___x_2146_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___f_2145_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
return v___x_2146_;
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
v_a_2147_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2143_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2143_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec(v_cfg_2134_);
v_a_2155_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2139_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2139_);
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
lean_dec(v_cfg_2134_);
return v___x_2138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___boxed(lean_object* v_x_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(v_x_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
lean_dec(v_a_2169_);
lean_dec_ref(v_a_2168_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush(lean_object* v_x_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(v_x_2172_, v_a_2173_, v_a_2174_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___boxed(lean_object* v_x_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush(v_x_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
lean_dec(v_a_2191_);
lean_dec_ref(v_a_2190_);
lean_dec(v_a_2189_);
lean_dec_ref(v_a_2188_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
lean_dec(v_a_2185_);
lean_dec_ref(v_a_2184_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1(){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2199_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1));
v___x_2201_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__1));
v___x_2202_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___boxed), 10, 0);
v___x_2203_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2199_, v___x_2200_, v___x_2201_, v___x_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___boxed(lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1();
return v_res_2205_;
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
