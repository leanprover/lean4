// Lean compiler output
// Module: Lean.Linter.Clippy.UnnecessarySeqFocus
// Imports: public import Lean.Elab.Command public import Lean.Linter.Basic
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
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedInfoTree_default;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_instMonadST(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_instBEqRange_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instHashableRange_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_instOrdNat___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_lexOrd___redArg(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_runST___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValueClippy(lean_object*, lean_object*);
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "clippy"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__2_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unnecessarySeqFocus"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__2_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__2_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(8, 147, 180, 72, 251, 158, 200, 109)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__2_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 88, 152, 68, 22, 35, 41, 205)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__4_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "enable the 'unnecessary <;>' linter"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__4_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__4_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__5_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__4_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__5_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__5_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__8_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Clippy"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__8_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__8_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__8_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(122, 129, 4, 127, 245, 52, 40, 126)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(143, 234, 138, 151, 255, 129, 205, 113)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 217, 95, 204, 138, 135, 218, 0)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__2_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(245, 224, 14, 189, 11, 155, 188, 234)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_linter_clippy_unnecessarySeqFocus;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_multigoalKindsRef;
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKinds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKinds___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__2_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "tacticNext_=>_"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__2_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__2_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__2_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 21, 53, 2, 17, 158, 67, 66)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 66, 138, 83, 251, 171, 29, 196)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "anyGoals"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(168, 19, 163, 3, 232, 106, 175, 32)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "case"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 244, 120, 128, 139, 198, 139, 51)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "case'"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 21, 185, 205, 238, 88, 7, 106)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__13_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "convNext__=>_"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__13_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__13_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__13_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 255, 234, 0, 142, 69, 158, 51)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(80, 55, 182, 70, 128, 26, 115, 15)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(97, 41, 143, 75, 238, 57, 26, 246)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(241, 23, 91, 126, 214, 77, 25, 163)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 157, 98, 160, 189, 128, 94, 31)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__19_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rotateLeft"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__19_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__19_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__19_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 201, 198, 124, 10, 198, 250, 123)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__21_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rotateRight"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__21_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__21_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__21_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(98, 177, 153, 112, 69, 167, 66, 136)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__23_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "show"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__23_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__23_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__23_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 147, 62, 103, 130, 224, 84, 63)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__25_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tacticStop_"};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__25_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__25_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__25_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 187, 217, 116, 133, 153, 2, 108)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__27_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*14, .m_other = 0, .m_tag = 246}, .m_size = 14, .m_capacity = 14, .m_data = {((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__27_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__27_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_isMultigoalKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_isMultigoalKind___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__0 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__0_value;
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_2),((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__1 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__1_value;
static const lean_string_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "conv_<;>_"};
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__2 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__2_value;
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_3),((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 57, 152, 10, 187, 180, 111, 39)}};
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__3 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__3_value;
LEAN_EXPORT uint8_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___boxed(lean_object*);
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__0;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instBEqRange_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__2 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__2_value;
static const lean_closure_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instHashableRange_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__3 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getPath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getPath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9;
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14;
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0;
static lean_once_cell_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__11___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___closed__1_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0_value;
static const lean_array_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__0 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__0_value;
static const lean_closure_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__0_value)} };
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__1 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__1_value;
static const lean_string_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "UnnecessarySeqFocus"};
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__2 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__2_value;
static const lean_string_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "unnecessarySeqFocusLinter"};
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__3 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__3_value;
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__6_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__7_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__8_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(122, 129, 4, 127, 245, 52, 40, 126)}};
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_2),((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(198, 152, 129, 0, 165, 172, 199, 105)}};
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_3),((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__3_value),LEAN_SCALAR_PTR_LITERAL(162, 211, 208, 179, 54, 41, 152, 90)}};
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value;
static const lean_ctor_object l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__1_value),((lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value)}};
static const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__5 = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter = (const lean_object*)&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = ((lean_object*)(l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__3_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__5_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn___closed__9_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_));
v___x_61_ = l_Lean_Option_register___at___00__private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4__spec__0(v___x_58_, v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_();
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = l_Lean_NameSet_empty;
v___x_66_ = lean_st_mk_ref(v___x_65_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2____boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2_();
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKind(lean_object* v_k_70_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_72_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_multigoalKindsRef;
v___x_73_ = lean_st_ref_take(v___x_72_);
v___x_74_ = l_Lean_NameSet_insert(v___x_73_, v_k_70_);
v___x_75_ = lean_st_ref_set(v___x_72_, v___x_74_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKind___boxed(lean_object* v_k_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKind(v_k_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0(lean_object* v_as_80_, size_t v_i_81_, size_t v_stop_82_, lean_object* v_b_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = lean_usize_dec_eq(v_i_81_, v_stop_82_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; size_t v___x_87_; size_t v___x_88_; 
v___x_85_ = lean_array_uget_borrowed(v_as_80_, v_i_81_);
lean_inc(v___x_85_);
v___x_86_ = l_Lean_NameSet_insert(v_b_83_, v___x_85_);
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_add(v_i_81_, v___x_87_);
v_i_81_ = v___x_88_;
v_b_83_ = v___x_86_;
goto _start;
}
else
{
return v_b_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0___boxed(lean_object* v_as_90_, lean_object* v_i_91_, lean_object* v_stop_92_, lean_object* v_b_93_){
_start:
{
size_t v_i_boxed_94_; size_t v_stop_boxed_95_; lean_object* v_res_96_; 
v_i_boxed_94_ = lean_unbox_usize(v_i_91_);
lean_dec(v_i_91_);
v_stop_boxed_95_ = lean_unbox_usize(v_stop_92_);
lean_dec(v_stop_92_);
v_res_96_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0(v_as_90_, v_i_boxed_94_, v_stop_boxed_95_, v_b_93_);
lean_dec_ref(v_as_90_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKinds(lean_object* v_ks_97_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___y_102_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_99_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_multigoalKindsRef;
v___x_100_ = lean_st_ref_take(v___x_99_);
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_array_get_size(v_ks_97_);
v___x_107_ = lean_nat_dec_lt(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
v___y_102_ = v___x_100_;
goto v___jp_101_;
}
else
{
uint8_t v___x_108_; 
v___x_108_ = lean_nat_dec_le(v___x_106_, v___x_106_);
if (v___x_108_ == 0)
{
if (v___x_107_ == 0)
{
v___y_102_ = v___x_100_;
goto v___jp_101_;
}
else
{
size_t v___x_109_; size_t v___x_110_; lean_object* v___x_111_; 
v___x_109_ = ((size_t)0ULL);
v___x_110_ = lean_usize_of_nat(v___x_106_);
v___x_111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0(v_ks_97_, v___x_109_, v___x_110_, v___x_100_);
v___y_102_ = v___x_111_;
goto v___jp_101_;
}
}
else
{
size_t v___x_112_; size_t v___x_113_; lean_object* v___x_114_; 
v___x_112_ = ((size_t)0ULL);
v___x_113_ = lean_usize_of_nat(v___x_106_);
v___x_114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0(v_ks_97_, v___x_112_, v___x_113_, v___x_100_);
v___y_102_ = v___x_114_;
goto v___jp_101_;
}
}
v___jp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_st_ref_set(v___x_99_, v___y_102_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKinds___boxed(lean_object* v_ks_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKinds(v_ks_115_);
lean_dec_ref(v_ks_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn___closed__27_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_));
v___x_238_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_addBuiltinMultigoalKinds(v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2____boxed(lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_();
return v_res_240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_isMultigoalKind(lean_object* v_k_241_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_multigoalKindsRef;
v___x_244_ = lean_st_ref_get(v___x_243_);
v___x_245_ = l_Lean_NameSet_contains(v___x_244_, v_k_241_);
lean_dec(v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_isMultigoalKind___boxed(lean_object* v_k_246_, lean_object* v_a_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_isMultigoalKind(v_k_246_);
lean_dec(v_k_246_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus(lean_object* v_k_263_){
_start:
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = ((lean_object*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__1));
v___x_265_ = lean_name_eq(v_k_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = ((lean_object*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__3));
v___x_267_ = lean_name_eq(v_k_263_, v___x_266_);
return v___x_267_;
}
else
{
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___boxed(lean_object* v_k_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus(v_k_268_);
lean_dec(v_k_268_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__0(void){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_instMonadST(lean_box(0));
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__1(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__0, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__0_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__0);
v___x_273_ = l_StateRefT_x27_instMonad___redArg(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___lam__0___boxed(lean_object* v_x_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___lam__0(v_x_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg(lean_object* v_stx_281_, lean_object* v_a_282_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__1, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__1_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__1);
if (lean_obj_tag(v_stx_281_) == 1)
{
lean_object* v_kind_285_; lean_object* v_args_286_; lean_object* v___f_287_; lean_object* v___y_289_; uint8_t v___y_304_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_kind_285_ = lean_ctor_get(v_stx_281_, 1);
v_args_286_ = lean_ctor_get(v_stx_281_, 2);
lean_inc_ref(v_args_286_);
v___f_287_ = lean_alloc_closure((void*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___lam__0___boxed), 4, 0);
v___x_314_ = ((lean_object*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__1));
v___x_315_ = lean_name_eq(v_kind_285_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__3));
v___x_317_ = lean_name_eq(v_kind_285_, v___x_316_);
v___y_304_ = v___x_317_;
goto v___jp_303_;
}
else
{
v___y_304_ = v___x_315_;
goto v___jp_303_;
}
v___jp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_array_get_size(v_args_286_);
v___x_292_ = lean_box(0);
v___x_293_ = lean_nat_dec_lt(v___x_290_, v___x_291_);
if (v___x_293_ == 0)
{
lean_dec_ref(v___f_287_);
lean_dec_ref(v_args_286_);
return v___x_292_;
}
else
{
uint8_t v___x_294_; 
v___x_294_ = lean_nat_dec_le(v___x_291_, v___x_291_);
if (v___x_294_ == 0)
{
if (v___x_293_ == 0)
{
lean_dec_ref(v___f_287_);
lean_dec_ref(v_args_286_);
return v___x_292_;
}
else
{
size_t v___x_295_; size_t v___x_296_; lean_object* v___x_749__overap_297_; lean_object* v___x_298_; 
v___x_295_ = ((size_t)0ULL);
v___x_296_ = lean_usize_of_nat(v___x_291_);
v___x_749__overap_297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_284_, v___f_287_, v_args_286_, v___x_295_, v___x_296_, v___x_292_);
lean_inc(v___y_289_);
v___x_298_ = lean_apply_2(v___x_749__overap_297_, v___y_289_, lean_box(0));
return v___x_298_;
}
}
else
{
size_t v___x_299_; size_t v___x_300_; lean_object* v___x_754__overap_301_; lean_object* v___x_302_; 
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_of_nat(v___x_291_);
v___x_754__overap_301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_284_, v___f_287_, v_args_286_, v___x_299_, v___x_300_, v___x_292_);
lean_inc(v___y_289_);
v___x_302_ = lean_apply_2(v___x_754__overap_301_, v___y_289_, lean_box(0));
return v___x_302_;
}
}
}
v___jp_303_:
{
if (v___y_304_ == 0)
{
lean_dec_ref(v_stx_281_);
v___y_289_ = v_a_282_;
goto v___jp_288_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Syntax_getRange_x3f(v_stx_281_, v___y_304_);
if (lean_obj_tag(v___x_305_) == 1)
{
lean_object* v_val_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_val_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_val_306_);
lean_dec_ref(v___x_305_);
v___x_307_ = lean_st_ref_take(v_a_282_);
v___x_308_ = ((lean_object*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__2));
v___x_309_ = ((lean_object*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___closed__3));
v___x_310_ = 0;
v___x_311_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_311_, 0, v_stx_281_);
lean_ctor_set_uint8(v___x_311_, sizeof(void*)*1, v___x_310_);
v___x_312_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_308_, v___x_309_, v___x_307_, v_val_306_, v___x_311_);
v___x_313_ = lean_st_ref_set(v_a_282_, v___x_312_);
v___y_289_ = v_a_282_;
goto v___jp_288_;
}
else
{
lean_dec(v___x_305_);
lean_dec_ref(v_stx_281_);
v___y_289_ = v_a_282_;
goto v___jp_288_;
}
}
}
}
else
{
lean_object* v___x_318_; 
lean_dec(v_stx_281_);
v___x_318_ = lean_box(0);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___lam__0(lean_object* v_x_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg(v___y_320_, v___y_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg___boxed(lean_object* v_stx_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg(v_stx_324_, v_a_325_);
lean_dec(v_a_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics(lean_object* v_00_u03c9_328_, lean_object* v_stx_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg(v_stx_329_, v_a_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___boxed(lean_object* v_00_u03c9_333_, lean_object* v_stx_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics(v_00_u03c9_333_, v_stx_334_, v_a_335_);
lean_dec(v_a_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getPath(lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
lean_object* v___x_341_; 
lean_dec_ref(v_x_339_);
v___x_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_341_, 0, v_x_338_);
return v___x_341_;
}
else
{
lean_object* v_head_342_; lean_object* v_tail_343_; lean_object* v_fst_344_; lean_object* v_snd_345_; lean_object* v_size_346_; uint8_t v___x_347_; 
lean_dec_ref(v_x_338_);
v_head_342_ = lean_ctor_get(v_x_340_, 0);
v_tail_343_ = lean_ctor_get(v_x_340_, 1);
v_fst_344_ = lean_ctor_get(v_head_342_, 0);
v_snd_345_ = lean_ctor_get(v_head_342_, 1);
v_size_346_ = lean_ctor_get(v_x_339_, 2);
v___x_347_ = lean_nat_dec_eq(v_size_346_, v_fst_344_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
lean_dec_ref(v_x_339_);
v___x_348_ = lean_box(0);
return v___x_348_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_350_ = l_Lean_PersistentArray_get_x21___redArg(v___x_349_, v_x_339_, v_snd_345_);
lean_dec_ref(v_x_339_);
if (lean_obj_tag(v___x_350_) == 1)
{
lean_object* v_i_351_; lean_object* v_children_352_; 
v_i_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc_ref(v_i_351_);
v_children_352_ = lean_ctor_get(v___x_350_, 1);
lean_inc_ref(v_children_352_);
lean_dec_ref(v___x_350_);
v_x_338_ = v_i_351_;
v_x_339_ = v_children_352_;
v_x_340_ = v_tail_343_;
goto _start;
}
else
{
lean_object* v___x_354_; 
lean_dec(v___x_350_);
v___x_354_ = lean_box(0);
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_getPath___boxed(lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_getPath(v_x_355_, v_x_356_, v_x_357_);
lean_dec(v_x_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(lean_object* v_a_359_, lean_object* v_x_360_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
lean_object* v___x_361_; 
v___x_361_ = lean_box(0);
return v___x_361_;
}
else
{
lean_object* v_key_362_; lean_object* v_value_363_; lean_object* v_tail_364_; uint8_t v___x_365_; 
v_key_362_ = lean_ctor_get(v_x_360_, 0);
v_value_363_ = lean_ctor_get(v_x_360_, 1);
v_tail_364_ = lean_ctor_get(v_x_360_, 2);
v___x_365_ = l_Lean_Syntax_instBEqRange_beq(v_key_362_, v_a_359_);
if (v___x_365_ == 0)
{
v_x_360_ = v_tail_364_;
goto _start;
}
else
{
lean_object* v___x_367_; 
lean_inc(v_value_363_);
v___x_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_367_, 0, v_value_363_);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg___boxed(lean_object* v_a_368_, lean_object* v_x_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_a_368_, v_x_369_);
lean_dec(v_x_369_);
lean_dec_ref(v_a_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(lean_object* v_m_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_buckets_373_; lean_object* v___x_374_; uint64_t v___x_375_; uint64_t v___x_376_; uint64_t v___x_377_; uint64_t v_fold_378_; uint64_t v___x_379_; uint64_t v___x_380_; uint64_t v___x_381_; size_t v___x_382_; size_t v___x_383_; size_t v___x_384_; size_t v___x_385_; size_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_buckets_373_ = lean_ctor_get(v_m_371_, 1);
v___x_374_ = lean_array_get_size(v_buckets_373_);
v___x_375_ = l_Lean_Syntax_instHashableRange_hash(v_a_372_);
v___x_376_ = 32ULL;
v___x_377_ = lean_uint64_shift_right(v___x_375_, v___x_376_);
v_fold_378_ = lean_uint64_xor(v___x_375_, v___x_377_);
v___x_379_ = 16ULL;
v___x_380_ = lean_uint64_shift_right(v_fold_378_, v___x_379_);
v___x_381_ = lean_uint64_xor(v_fold_378_, v___x_380_);
v___x_382_ = lean_uint64_to_usize(v___x_381_);
v___x_383_ = lean_usize_of_nat(v___x_374_);
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_sub(v___x_383_, v___x_384_);
v___x_386_ = lean_usize_land(v___x_382_, v___x_385_);
v___x_387_ = lean_array_uget_borrowed(v_buckets_373_, v___x_386_);
v___x_388_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_a_372_, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg___boxed(lean_object* v_m_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v_m_389_, v_a_390_);
lean_dec_ref(v_a_390_);
lean_dec_ref(v_m_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(lean_object* v_a_392_, lean_object* v_x_393_){
_start:
{
if (lean_obj_tag(v_x_393_) == 0)
{
return v_x_393_;
}
else
{
lean_object* v_key_394_; lean_object* v_value_395_; lean_object* v_tail_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_405_; 
v_key_394_ = lean_ctor_get(v_x_393_, 0);
v_value_395_ = lean_ctor_get(v_x_393_, 1);
v_tail_396_ = lean_ctor_get(v_x_393_, 2);
v_isSharedCheck_405_ = !lean_is_exclusive(v_x_393_);
if (v_isSharedCheck_405_ == 0)
{
v___x_398_ = v_x_393_;
v_isShared_399_ = v_isSharedCheck_405_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_tail_396_);
lean_inc(v_value_395_);
lean_inc(v_key_394_);
lean_dec(v_x_393_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_405_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
uint8_t v___x_400_; 
v___x_400_ = l_Lean_Syntax_instBEqRange_beq(v_key_394_, v_a_392_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_392_, v_tail_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 2, v___x_401_);
v___x_403_ = v___x_398_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_key_394_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_value_395_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
else
{
lean_del_object(v___x_398_);
lean_dec(v_value_395_);
lean_dec(v_key_394_);
return v_tail_396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg___boxed(lean_object* v_a_406_, lean_object* v_x_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_406_, v_x_407_);
lean_dec_ref(v_a_406_);
return v_res_408_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(lean_object* v_a_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
uint8_t v___x_411_; 
v___x_411_ = 0;
return v___x_411_;
}
else
{
lean_object* v_key_412_; lean_object* v_tail_413_; uint8_t v___x_414_; 
v_key_412_ = lean_ctor_get(v_x_410_, 0);
v_tail_413_ = lean_ctor_get(v_x_410_, 2);
v___x_414_ = l_Lean_Syntax_instBEqRange_beq(v_key_412_, v_a_409_);
if (v___x_414_ == 0)
{
v_x_410_ = v_tail_413_;
goto _start;
}
else
{
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg___boxed(lean_object* v_a_416_, lean_object* v_x_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_416_, v_x_417_);
lean_dec(v_x_417_);
lean_dec_ref(v_a_416_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(lean_object* v_m_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_size_422_; lean_object* v_buckets_423_; lean_object* v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v___x_427_; uint64_t v_fold_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; size_t v___x_436_; lean_object* v_bkt_437_; uint8_t v___x_438_; 
v_size_422_ = lean_ctor_get(v_m_420_, 0);
v_buckets_423_ = lean_ctor_get(v_m_420_, 1);
v___x_424_ = lean_array_get_size(v_buckets_423_);
v___x_425_ = l_Lean_Syntax_instHashableRange_hash(v_a_421_);
v___x_426_ = 32ULL;
v___x_427_ = lean_uint64_shift_right(v___x_425_, v___x_426_);
v_fold_428_ = lean_uint64_xor(v___x_425_, v___x_427_);
v___x_429_ = 16ULL;
v___x_430_ = lean_uint64_shift_right(v_fold_428_, v___x_429_);
v___x_431_ = lean_uint64_xor(v_fold_428_, v___x_430_);
v___x_432_ = lean_uint64_to_usize(v___x_431_);
v___x_433_ = lean_usize_of_nat(v___x_424_);
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_sub(v___x_433_, v___x_434_);
v___x_436_ = lean_usize_land(v___x_432_, v___x_435_);
v_bkt_437_ = lean_array_uget_borrowed(v_buckets_423_, v___x_436_);
v___x_438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_421_, v_bkt_437_);
if (v___x_438_ == 0)
{
return v_m_420_;
}
else
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_451_; 
lean_inc(v_bkt_437_);
lean_inc_ref(v_buckets_423_);
lean_inc(v_size_422_);
v_isSharedCheck_451_ = !lean_is_exclusive(v_m_420_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; lean_object* v_unused_453_; 
v_unused_452_ = lean_ctor_get(v_m_420_, 1);
lean_dec(v_unused_452_);
v_unused_453_ = lean_ctor_get(v_m_420_, 0);
lean_dec(v_unused_453_);
v___x_440_ = v_m_420_;
v_isShared_441_ = v_isSharedCheck_451_;
goto v_resetjp_439_;
}
else
{
lean_dec(v_m_420_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_451_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v_buckets_x27_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_442_ = lean_box(0);
v_buckets_x27_443_ = lean_array_uset(v_buckets_423_, v___x_436_, v___x_442_);
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_nat_sub(v_size_422_, v___x_444_);
lean_dec(v_size_422_);
v___x_446_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_421_, v_bkt_437_);
v___x_447_ = lean_array_uset(v_buckets_x27_443_, v___x_436_, v___x_446_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_447_);
lean_ctor_set(v___x_440_, 0, v___x_445_);
v___x_449_ = v___x_440_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg___boxed(lean_object* v_m_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v_m_454_, v_a_455_);
lean_dec_ref(v_a_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(lean_object* v_a_457_, lean_object* v_b_458_, lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_459_) == 0)
{
lean_dec(v_b_458_);
lean_dec_ref(v_a_457_);
return v_x_459_;
}
else
{
lean_object* v_key_460_; lean_object* v_value_461_; lean_object* v_tail_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_474_; 
v_key_460_ = lean_ctor_get(v_x_459_, 0);
v_value_461_ = lean_ctor_get(v_x_459_, 1);
v_tail_462_ = lean_ctor_get(v_x_459_, 2);
v_isSharedCheck_474_ = !lean_is_exclusive(v_x_459_);
if (v_isSharedCheck_474_ == 0)
{
v___x_464_ = v_x_459_;
v_isShared_465_ = v_isSharedCheck_474_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_tail_462_);
lean_inc(v_value_461_);
lean_inc(v_key_460_);
lean_dec(v_x_459_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_474_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v___x_466_; 
v___x_466_ = l_Lean_Syntax_instBEqRange_beq(v_key_460_, v_a_457_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(v_a_457_, v_b_458_, v_tail_462_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 2, v___x_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_key_460_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_value_461_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
else
{
lean_object* v___x_472_; 
lean_dec(v_value_461_);
lean_dec(v_key_460_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v_b_458_);
lean_ctor_set(v___x_464_, 0, v_a_457_);
v___x_472_ = v___x_464_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_457_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_b_458_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_tail_462_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14___redArg(lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
return v_x_475_;
}
else
{
lean_object* v_key_477_; lean_object* v_value_478_; lean_object* v_tail_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_502_; 
v_key_477_ = lean_ctor_get(v_x_476_, 0);
v_value_478_ = lean_ctor_get(v_x_476_, 1);
v_tail_479_ = lean_ctor_get(v_x_476_, 2);
v_isSharedCheck_502_ = !lean_is_exclusive(v_x_476_);
if (v_isSharedCheck_502_ == 0)
{
v___x_481_ = v_x_476_;
v_isShared_482_ = v_isSharedCheck_502_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_tail_479_);
lean_inc(v_value_478_);
lean_inc(v_key_477_);
lean_dec(v_x_476_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_502_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v___x_486_; uint64_t v_fold_487_; uint64_t v___x_488_; uint64_t v___x_489_; uint64_t v___x_490_; size_t v___x_491_; size_t v___x_492_; size_t v___x_493_; size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_483_ = lean_array_get_size(v_x_475_);
v___x_484_ = l_Lean_Syntax_instHashableRange_hash(v_key_477_);
v___x_485_ = 32ULL;
v___x_486_ = lean_uint64_shift_right(v___x_484_, v___x_485_);
v_fold_487_ = lean_uint64_xor(v___x_484_, v___x_486_);
v___x_488_ = 16ULL;
v___x_489_ = lean_uint64_shift_right(v_fold_487_, v___x_488_);
v___x_490_ = lean_uint64_xor(v_fold_487_, v___x_489_);
v___x_491_ = lean_uint64_to_usize(v___x_490_);
v___x_492_ = lean_usize_of_nat(v___x_483_);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_sub(v___x_492_, v___x_493_);
v___x_495_ = lean_usize_land(v___x_491_, v___x_494_);
v___x_496_ = lean_array_uget_borrowed(v_x_475_, v___x_495_);
lean_inc(v___x_496_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 2, v___x_496_);
v___x_498_ = v___x_481_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_key_477_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_value_478_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v___x_496_);
v___x_498_ = v_reuseFailAlloc_501_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; 
v___x_499_ = lean_array_uset(v_x_475_, v___x_495_, v___x_498_);
v_x_475_ = v___x_499_;
v_x_476_ = v_tail_479_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13___redArg(lean_object* v_i_503_, lean_object* v_source_504_, lean_object* v_target_505_){
_start:
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_array_get_size(v_source_504_);
v___x_507_ = lean_nat_dec_lt(v_i_503_, v___x_506_);
if (v___x_507_ == 0)
{
lean_dec_ref(v_source_504_);
lean_dec(v_i_503_);
return v_target_505_;
}
else
{
lean_object* v_es_508_; lean_object* v___x_509_; lean_object* v_source_510_; lean_object* v_target_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_es_508_ = lean_array_fget(v_source_504_, v_i_503_);
v___x_509_ = lean_box(0);
v_source_510_ = lean_array_fset(v_source_504_, v_i_503_, v___x_509_);
v_target_511_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14___redArg(v_target_505_, v_es_508_);
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_nat_add(v_i_503_, v___x_512_);
lean_dec(v_i_503_);
v_i_503_ = v___x_513_;
v_source_504_ = v_source_510_;
v_target_505_ = v_target_511_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10___redArg(lean_object* v_data_515_){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v_nbuckets_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_516_ = lean_array_get_size(v_data_515_);
v___x_517_ = lean_unsigned_to_nat(2u);
v_nbuckets_518_ = lean_nat_mul(v___x_516_, v___x_517_);
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = lean_box(0);
v___x_521_ = lean_mk_array(v_nbuckets_518_, v___x_520_);
v___x_522_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13___redArg(v___x_519_, v_data_515_, v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(lean_object* v_m_523_, lean_object* v_a_524_, lean_object* v_b_525_){
_start:
{
lean_object* v_size_526_; lean_object* v_buckets_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_570_; 
v_size_526_ = lean_ctor_get(v_m_523_, 0);
v_buckets_527_ = lean_ctor_get(v_m_523_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_m_523_);
if (v_isSharedCheck_570_ == 0)
{
v___x_529_ = v_m_523_;
v_isShared_530_ = v_isSharedCheck_570_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_buckets_527_);
lean_inc(v_size_526_);
lean_dec(v_m_523_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_570_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; uint64_t v___x_532_; uint64_t v___x_533_; uint64_t v___x_534_; uint64_t v_fold_535_; uint64_t v___x_536_; uint64_t v___x_537_; uint64_t v___x_538_; size_t v___x_539_; size_t v___x_540_; size_t v___x_541_; size_t v___x_542_; size_t v___x_543_; lean_object* v_bkt_544_; uint8_t v___x_545_; 
v___x_531_ = lean_array_get_size(v_buckets_527_);
v___x_532_ = l_Lean_Syntax_instHashableRange_hash(v_a_524_);
v___x_533_ = 32ULL;
v___x_534_ = lean_uint64_shift_right(v___x_532_, v___x_533_);
v_fold_535_ = lean_uint64_xor(v___x_532_, v___x_534_);
v___x_536_ = 16ULL;
v___x_537_ = lean_uint64_shift_right(v_fold_535_, v___x_536_);
v___x_538_ = lean_uint64_xor(v_fold_535_, v___x_537_);
v___x_539_ = lean_uint64_to_usize(v___x_538_);
v___x_540_ = lean_usize_of_nat(v___x_531_);
v___x_541_ = ((size_t)1ULL);
v___x_542_ = lean_usize_sub(v___x_540_, v___x_541_);
v___x_543_ = lean_usize_land(v___x_539_, v___x_542_);
v_bkt_544_ = lean_array_uget_borrowed(v_buckets_527_, v___x_543_);
v___x_545_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_524_, v_bkt_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v_size_x27_547_; lean_object* v___x_548_; lean_object* v_buckets_x27_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_546_ = lean_unsigned_to_nat(1u);
v_size_x27_547_ = lean_nat_add(v_size_526_, v___x_546_);
lean_dec(v_size_526_);
lean_inc(v_bkt_544_);
v___x_548_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_548_, 0, v_a_524_);
lean_ctor_set(v___x_548_, 1, v_b_525_);
lean_ctor_set(v___x_548_, 2, v_bkt_544_);
v_buckets_x27_549_ = lean_array_uset(v_buckets_527_, v___x_543_, v___x_548_);
v___x_550_ = lean_unsigned_to_nat(4u);
v___x_551_ = lean_nat_mul(v_size_x27_547_, v___x_550_);
v___x_552_ = lean_unsigned_to_nat(3u);
v___x_553_ = lean_nat_div(v___x_551_, v___x_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_array_get_size(v_buckets_x27_549_);
v___x_555_ = lean_nat_dec_le(v___x_553_, v___x_554_);
lean_dec(v___x_553_);
if (v___x_555_ == 0)
{
lean_object* v_val_556_; lean_object* v___x_558_; 
v_val_556_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10___redArg(v_buckets_x27_549_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v_val_556_);
lean_ctor_set(v___x_529_, 0, v_size_x27_547_);
v___x_558_ = v___x_529_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_size_x27_547_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_val_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
else
{
lean_object* v___x_561_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v_buckets_x27_549_);
lean_ctor_set(v___x_529_, 0, v_size_x27_547_);
v___x_561_ = v___x_529_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_size_x27_547_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_buckets_x27_549_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
lean_object* v___x_563_; lean_object* v_buckets_x27_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
lean_inc(v_bkt_544_);
v___x_563_ = lean_box(0);
v_buckets_x27_564_ = lean_array_uset(v_buckets_527_, v___x_543_, v___x_563_);
v___x_565_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(v_a_524_, v_b_525_, v_bkt_544_);
v___x_566_ = lean_array_uset(v_buckets_x27_564_, v___x_543_, v___x_565_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v___x_566_);
v___x_568_ = v___x_529_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_size_526_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(5u);
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_nat_mod(v___x_573_, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4);
v___x_576_ = lean_unsigned_to_nat(5u);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_box(0);
v___x_579_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5);
v___x_580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_nat_mod(v___x_582_, v___x_581_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0);
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6);
v___x_588_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v___x_587_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_unsigned_to_nat(2u);
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_nat_mod(v___x_591_, v___x_590_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2);
v___x_594_ = lean_unsigned_to_nat(2u);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
return v___x_595_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7);
v___x_597_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3);
v___x_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___x_596_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8);
v___x_600_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_599_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9);
v___x_605_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_604_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11);
v___x_608_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12);
v___x_611_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13);
v___x_614_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1);
v___x_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___x_613_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg(lean_object* v_multigoals_616_, lean_object* v_x_617_, lean_object* v_a_618_){
_start:
{
switch(lean_obj_tag(v_x_617_))
{
case 0:
{
lean_object* v_t_620_; 
v_t_620_ = lean_ctor_get(v_x_617_, 1);
lean_inc_ref(v_t_620_);
lean_dec_ref(v_x_617_);
v_x_617_ = v_t_620_;
goto _start;
}
case 1:
{
lean_object* v_i_622_; lean_object* v_children_623_; lean_object* v_snd_625_; lean_object* v_snd_629_; 
v_i_622_ = lean_ctor_get(v_x_617_, 0);
lean_inc_ref(v_i_622_);
v_children_623_ = lean_ctor_get(v_x_617_, 1);
lean_inc_ref(v_children_623_);
lean_dec_ref(v_x_617_);
if (lean_obj_tag(v_i_622_) == 0)
{
lean_object* v_i_632_; lean_object* v_toElabInfo_633_; lean_object* v_goalsBefore_634_; lean_object* v_stx_635_; uint8_t v___x_636_; lean_object* v___x_637_; 
v_i_632_ = lean_ctor_get(v_i_622_, 0);
v_toElabInfo_633_ = lean_ctor_get(v_i_632_, 0);
v_goalsBefore_634_ = lean_ctor_get(v_i_632_, 2);
v_stx_635_ = lean_ctor_get(v_toElabInfo_633_, 1);
v___x_636_ = 1;
v___x_637_ = l_Lean_Syntax_getRange_x3f(v_stx_635_, v___x_636_);
if (lean_obj_tag(v___x_637_) == 1)
{
lean_object* v_val_638_; lean_object* v___y_640_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_val_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_638_);
lean_dec_ref(v___x_637_);
v___x_642_ = lean_st_ref_get(v_a_618_);
v___x_643_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v___x_642_, v_val_638_);
lean_dec(v___x_642_);
if (lean_obj_tag(v___x_643_) == 1)
{
lean_object* v_val_644_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; lean_object* v___y_662_; uint8_t v___y_687_; 
v_val_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_val_644_);
lean_dec_ref(v___x_643_);
lean_inc(v_stx_635_);
v___x_658_ = l_Lean_Syntax_getKind(v_stx_635_);
v___x_659_ = ((lean_object*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__1));
v___x_660_ = lean_name_eq(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_689_; uint8_t v___x_690_; lean_object* v___y_692_; uint8_t v___y_708_; 
v___x_689_ = ((lean_object*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_isSeqFocus___closed__3));
v___x_690_ = lean_name_eq(v___x_658_, v___x_689_);
lean_dec(v___x_658_);
if (v___x_690_ == 0)
{
lean_object* v___x_710_; 
lean_dec(v_val_644_);
lean_dec(v_val_638_);
lean_dec_ref(v_i_622_);
v___x_710_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_616_, v_children_623_, v_a_618_);
lean_dec_ref(v_children_623_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_711_ = l_List_lengthTR___redArg(v_goalsBefore_634_);
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_dec_eq(v___x_711_, v___x_712_);
lean_dec(v___x_711_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = l_Lean_Syntax_getArg(v_stx_635_, v___x_714_);
v___x_716_ = l_Lean_Syntax_getKind(v___x_715_);
v___x_717_ = l_Lean_NameSet_contains(v_multigoals_616_, v___x_716_);
lean_dec(v___x_716_);
if (v___x_717_ == 0)
{
v___y_708_ = v___x_690_;
goto v___jp_707_;
}
else
{
v___y_708_ = v___x_713_;
goto v___jp_707_;
}
}
else
{
goto v___jp_694_;
}
}
v___jp_691_:
{
lean_object* v___x_693_; 
v___x_693_ = lean_st_ref_take(v_a_618_);
if (lean_obj_tag(v___y_692_) == 0)
{
v___y_646_ = v___x_693_;
v___y_647_ = v___x_660_;
goto v___jp_645_;
}
else
{
v___y_646_ = v___x_693_;
v___y_647_ = v___x_690_;
goto v___jp_645_;
}
}
v___jp_694_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14);
lean_inc_ref(v_children_623_);
v___x_697_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_getPath(v_i_622_, v_children_623_, v___x_696_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_698_; 
v___x_698_ = lean_box(0);
v___y_692_ = v___x_698_;
goto v___jp_691_;
}
else
{
lean_object* v_val_699_; 
v_val_699_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_val_699_);
lean_dec_ref(v___x_697_);
if (lean_obj_tag(v_val_699_) == 0)
{
lean_object* v_i_700_; lean_object* v_goalsAfter_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_i_700_ = lean_ctor_get(v_val_699_, 0);
lean_inc_ref(v_i_700_);
lean_dec_ref(v_val_699_);
v_goalsAfter_701_ = lean_ctor_get(v_i_700_, 4);
lean_inc(v_goalsAfter_701_);
lean_dec_ref(v_i_700_);
v___x_702_ = l_List_lengthTR___redArg(v_goalsAfter_701_);
lean_dec(v_goalsAfter_701_);
v___x_703_ = lean_nat_dec_eq(v___x_702_, v___x_695_);
lean_dec(v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
v___x_704_ = lean_box(0);
v___y_692_ = v___x_704_;
goto v___jp_691_;
}
else
{
lean_object* v___x_705_; 
v___x_705_ = ((lean_object*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10));
v___y_692_ = v___x_705_;
goto v___jp_691_;
}
}
else
{
lean_object* v___x_706_; 
lean_dec(v_val_699_);
v___x_706_ = lean_box(0);
v___y_692_ = v___x_706_;
goto v___jp_691_;
}
}
}
v___jp_707_:
{
if (v___y_708_ == 0)
{
lean_object* v___x_709_; 
lean_dec_ref(v_i_622_);
v___x_709_ = lean_box(0);
v___y_692_ = v___x_709_;
goto v___jp_691_;
}
else
{
goto v___jp_694_;
}
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
lean_dec(v___x_658_);
v___x_718_ = l_List_lengthTR___redArg(v_goalsBefore_634_);
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_nat_dec_eq(v___x_718_, v___x_719_);
lean_dec(v___x_718_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = l_Lean_Syntax_getArg(v_stx_635_, v___x_721_);
v___x_723_ = l_Lean_Syntax_getKind(v___x_722_);
v___x_724_ = l_Lean_NameSet_contains(v_multigoals_616_, v___x_723_);
lean_dec(v___x_723_);
if (v___x_724_ == 0)
{
v___y_687_ = v___x_660_;
goto v___jp_686_;
}
else
{
v___y_687_ = v___x_720_;
goto v___jp_686_;
}
}
else
{
goto v___jp_673_;
}
}
v___jp_645_:
{
if (v___y_647_ == 0)
{
lean_object* v___x_648_; 
lean_dec(v_val_644_);
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v___y_646_, v_val_638_);
lean_dec(v_val_638_);
v_snd_629_ = v___x_648_;
goto v___jp_628_;
}
else
{
lean_object* v_stx_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_657_; 
v_stx_649_ = lean_ctor_get(v_val_644_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_val_644_);
if (v_isSharedCheck_657_ == 0)
{
v___x_651_ = v_val_644_;
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_stx_649_);
lean_dec(v_val_644_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_657_;
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
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_stx_649_);
v___x_654_ = v_reuseFailAlloc_656_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; 
lean_ctor_set_uint8(v___x_654_, sizeof(void*)*1, v___x_636_);
v___x_655_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v___y_646_, v_val_638_, v___x_654_);
v_snd_629_ = v___x_655_;
goto v___jp_628_;
}
}
}
}
v___jp_661_:
{
lean_object* v___x_663_; 
v___x_663_ = lean_st_ref_take(v_a_618_);
if (lean_obj_tag(v___y_662_) == 0)
{
lean_dec(v_val_644_);
v___y_640_ = v___x_663_;
goto v___jp_639_;
}
else
{
if (v___x_660_ == 0)
{
lean_dec(v_val_644_);
v___y_640_ = v___x_663_;
goto v___jp_639_;
}
else
{
lean_object* v_stx_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_672_; 
v_stx_664_ = lean_ctor_get(v_val_644_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_val_644_);
if (v_isSharedCheck_672_ == 0)
{
v___x_666_ = v_val_644_;
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_stx_664_);
lean_dec(v_val_644_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_stx_664_);
v___x_669_ = v_reuseFailAlloc_671_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; 
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*1, v___x_636_);
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v___x_663_, v_val_638_, v___x_669_);
v_snd_625_ = v___x_670_;
goto v___jp_624_;
}
}
}
}
}
v___jp_673_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9);
lean_inc_ref(v_children_623_);
v___x_676_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_getPath(v_i_622_, v_children_623_, v___x_675_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v___x_677_; 
v___x_677_ = lean_box(0);
v___y_662_ = v___x_677_;
goto v___jp_661_;
}
else
{
lean_object* v_val_678_; 
v_val_678_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_val_678_);
lean_dec_ref(v___x_676_);
if (lean_obj_tag(v_val_678_) == 0)
{
lean_object* v_i_679_; lean_object* v_goalsAfter_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_i_679_ = lean_ctor_get(v_val_678_, 0);
lean_inc_ref(v_i_679_);
lean_dec_ref(v_val_678_);
v_goalsAfter_680_ = lean_ctor_get(v_i_679_, 4);
lean_inc(v_goalsAfter_680_);
lean_dec_ref(v_i_679_);
v___x_681_ = l_List_lengthTR___redArg(v_goalsAfter_680_);
lean_dec(v_goalsAfter_680_);
v___x_682_ = lean_nat_dec_eq(v___x_681_, v___x_674_);
lean_dec(v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; 
v___x_683_ = lean_box(0);
v___y_662_ = v___x_683_;
goto v___jp_661_;
}
else
{
lean_object* v___x_684_; 
v___x_684_ = ((lean_object*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10));
v___y_662_ = v___x_684_;
goto v___jp_661_;
}
}
else
{
lean_object* v___x_685_; 
lean_dec(v_val_678_);
v___x_685_ = lean_box(0);
v___y_662_ = v___x_685_;
goto v___jp_661_;
}
}
}
v___jp_686_:
{
if (v___y_687_ == 0)
{
lean_object* v___x_688_; 
lean_dec_ref(v_i_622_);
v___x_688_ = lean_box(0);
v___y_662_ = v___x_688_;
goto v___jp_661_;
}
else
{
goto v___jp_673_;
}
}
}
else
{
lean_object* v___x_725_; 
lean_dec(v___x_643_);
lean_dec(v_val_638_);
lean_dec_ref(v_i_622_);
v___x_725_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_616_, v_children_623_, v_a_618_);
lean_dec_ref(v_children_623_);
return v___x_725_;
}
v___jp_639_:
{
lean_object* v___x_641_; 
v___x_641_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v___y_640_, v_val_638_);
lean_dec(v_val_638_);
v_snd_625_ = v___x_641_;
goto v___jp_624_;
}
}
else
{
lean_object* v___x_726_; 
lean_dec(v___x_637_);
lean_dec_ref(v_i_622_);
v___x_726_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_616_, v_children_623_, v_a_618_);
lean_dec_ref(v_children_623_);
return v___x_726_;
}
}
else
{
lean_object* v___x_727_; 
lean_dec_ref(v_i_622_);
v___x_727_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_616_, v_children_623_, v_a_618_);
lean_dec_ref(v_children_623_);
return v___x_727_;
}
v___jp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_st_ref_set(v_a_618_, v_snd_625_);
v___x_627_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_616_, v_children_623_, v_a_618_);
lean_dec_ref(v_children_623_);
return v___x_627_;
}
v___jp_628_:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_st_ref_set(v_a_618_, v_snd_629_);
v___x_631_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_616_, v_children_623_, v_a_618_);
lean_dec_ref(v_children_623_);
return v___x_631_;
}
}
default: 
{
lean_object* v___x_728_; 
lean_dec_ref(v_x_617_);
v___x_728_ = lean_box(0);
return v___x_728_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(lean_object* v_multigoals_729_, lean_object* v_as_730_, size_t v_i_731_, size_t v_stop_732_, lean_object* v_b_733_, lean_object* v___y_734_){
_start:
{
uint8_t v___x_736_; 
v___x_736_ = lean_usize_dec_eq(v_i_731_, v_stop_732_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; size_t v___x_739_; size_t v___x_740_; 
v___x_737_ = lean_array_uget_borrowed(v_as_730_, v_i_731_);
lean_inc(v___x_737_);
v___x_738_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg(v_multigoals_729_, v___x_737_, v___y_734_);
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_add(v_i_731_, v___x_739_);
v_i_731_ = v___x_740_;
v_b_733_ = v___x_738_;
goto _start;
}
else
{
return v_b_733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(lean_object* v_multigoals_742_, lean_object* v_x_743_, lean_object* v___y_744_){
_start:
{
if (lean_obj_tag(v_x_743_) == 0)
{
lean_object* v_cs_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_cs_746_ = lean_ctor_get(v_x_743_, 0);
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = lean_array_get_size(v_cs_746_);
v___x_749_ = lean_box(0);
v___x_750_ = lean_nat_dec_lt(v___x_747_, v___x_748_);
if (v___x_750_ == 0)
{
return v___x_749_;
}
else
{
uint8_t v___x_751_; 
v___x_751_ = lean_nat_dec_le(v___x_748_, v___x_748_);
if (v___x_751_ == 0)
{
if (v___x_750_ == 0)
{
return v___x_749_;
}
else
{
size_t v___x_752_; size_t v___x_753_; lean_object* v___x_754_; 
v___x_752_ = ((size_t)0ULL);
v___x_753_ = lean_usize_of_nat(v___x_748_);
v___x_754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_742_, v_cs_746_, v___x_752_, v___x_753_, v___x_749_, v___y_744_);
return v___x_754_;
}
}
else
{
size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
v___x_755_ = ((size_t)0ULL);
v___x_756_ = lean_usize_of_nat(v___x_748_);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_742_, v_cs_746_, v___x_755_, v___x_756_, v___x_749_, v___y_744_);
return v___x_757_;
}
}
}
else
{
lean_object* v_vs_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_vs_758_ = lean_ctor_get(v_x_743_, 0);
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = lean_array_get_size(v_vs_758_);
v___x_761_ = lean_box(0);
v___x_762_ = lean_nat_dec_lt(v___x_759_, v___x_760_);
if (v___x_762_ == 0)
{
return v___x_761_;
}
else
{
uint8_t v___x_763_; 
v___x_763_ = lean_nat_dec_le(v___x_760_, v___x_760_);
if (v___x_763_ == 0)
{
if (v___x_762_ == 0)
{
return v___x_761_;
}
else
{
size_t v___x_764_; size_t v___x_765_; lean_object* v___x_766_; 
v___x_764_ = ((size_t)0ULL);
v___x_765_ = lean_usize_of_nat(v___x_760_);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_742_, v_vs_758_, v___x_764_, v___x_765_, v___x_761_, v___y_744_);
return v___x_766_;
}
}
else
{
size_t v___x_767_; size_t v___x_768_; lean_object* v___x_769_; 
v___x_767_ = ((size_t)0ULL);
v___x_768_ = lean_usize_of_nat(v___x_760_);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_742_, v_vs_758_, v___x_767_, v___x_768_, v___x_761_, v___y_744_);
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(lean_object* v_multigoals_770_, lean_object* v_as_771_, size_t v_i_772_, size_t v_stop_773_, lean_object* v_b_774_, lean_object* v___y_775_){
_start:
{
uint8_t v___x_777_; 
v___x_777_ = lean_usize_dec_eq(v_i_772_, v_stop_773_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; size_t v___x_780_; size_t v___x_781_; 
v___x_778_ = lean_array_uget_borrowed(v_as_771_, v_i_772_);
v___x_779_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_770_, v___x_778_, v___y_775_);
v___x_780_ = ((size_t)1ULL);
v___x_781_ = lean_usize_add(v_i_772_, v___x_780_);
v_i_772_ = v___x_781_;
v_b_774_ = v___x_779_;
goto _start;
}
else
{
return v_b_774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(lean_object* v_multigoals_783_, lean_object* v_x_784_, size_t v_x_785_, size_t v_x_786_, lean_object* v___y_787_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
lean_object* v_cs_789_; lean_object* v___x_790_; size_t v___x_791_; lean_object* v_j_792_; lean_object* v___x_793_; size_t v___x_794_; size_t v___x_795_; size_t v___x_796_; size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_cs_789_ = lean_ctor_get(v_x_784_, 0);
v___x_790_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0);
v___x_791_ = lean_usize_shift_right(v_x_785_, v_x_786_);
v_j_792_ = lean_usize_to_nat(v___x_791_);
v___x_793_ = lean_array_get_borrowed(v___x_790_, v_cs_789_, v_j_792_);
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_shift_left(v___x_794_, v_x_786_);
v___x_796_ = lean_usize_sub(v___x_795_, v___x_794_);
v___x_797_ = lean_usize_land(v_x_785_, v___x_796_);
v___x_798_ = ((size_t)5ULL);
v___x_799_ = lean_usize_sub(v_x_786_, v___x_798_);
v___x_800_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_783_, v___x_793_, v___x_797_, v___x_799_, v___y_787_);
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_add(v_j_792_, v___x_801_);
lean_dec(v_j_792_);
v___x_803_ = lean_array_get_size(v_cs_789_);
v___x_804_ = lean_box(0);
v___x_805_ = lean_nat_dec_lt(v___x_802_, v___x_803_);
if (v___x_805_ == 0)
{
lean_dec(v___x_802_);
return v___x_804_;
}
else
{
uint8_t v___x_806_; 
v___x_806_ = lean_nat_dec_le(v___x_803_, v___x_803_);
if (v___x_806_ == 0)
{
if (v___x_805_ == 0)
{
lean_dec(v___x_802_);
return v___x_804_;
}
else
{
size_t v___x_807_; size_t v___x_808_; lean_object* v___x_809_; 
v___x_807_ = lean_usize_of_nat(v___x_802_);
lean_dec(v___x_802_);
v___x_808_ = lean_usize_of_nat(v___x_803_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_783_, v_cs_789_, v___x_807_, v___x_808_, v___x_804_, v___y_787_);
return v___x_809_;
}
}
else
{
size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; 
v___x_810_ = lean_usize_of_nat(v___x_802_);
lean_dec(v___x_802_);
v___x_811_ = lean_usize_of_nat(v___x_803_);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_783_, v_cs_789_, v___x_810_, v___x_811_, v___x_804_, v___y_787_);
return v___x_812_;
}
}
}
else
{
lean_object* v_vs_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_vs_813_ = lean_ctor_get(v_x_784_, 0);
v___x_814_ = lean_usize_to_nat(v_x_785_);
v___x_815_ = lean_array_get_size(v_vs_813_);
v___x_816_ = lean_box(0);
v___x_817_ = lean_nat_dec_lt(v___x_814_, v___x_815_);
if (v___x_817_ == 0)
{
lean_dec(v___x_814_);
return v___x_816_;
}
else
{
uint8_t v___x_818_; 
v___x_818_ = lean_nat_dec_le(v___x_815_, v___x_815_);
if (v___x_818_ == 0)
{
if (v___x_817_ == 0)
{
lean_dec(v___x_814_);
return v___x_816_;
}
else
{
size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; 
v___x_819_ = lean_usize_of_nat(v___x_814_);
lean_dec(v___x_814_);
v___x_820_ = lean_usize_of_nat(v___x_815_);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_783_, v_vs_813_, v___x_819_, v___x_820_, v___x_816_, v___y_787_);
return v___x_821_;
}
}
else
{
size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; 
v___x_822_ = lean_usize_of_nat(v___x_814_);
lean_dec(v___x_814_);
v___x_823_ = lean_usize_of_nat(v___x_815_);
v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_783_, v_vs_813_, v___x_822_, v___x_823_, v___x_816_, v___y_787_);
return v___x_824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(lean_object* v_multigoals_825_, lean_object* v_t_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_root_829_; lean_object* v_tail_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_root_829_ = lean_ctor_get(v_t_826_, 0);
v_tail_830_ = lean_ctor_get(v_t_826_, 1);
v___x_831_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_825_, v_root_829_, v___y_827_);
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_array_get_size(v_tail_830_);
v___x_834_ = lean_box(0);
v___x_835_ = lean_nat_dec_lt(v___x_832_, v___x_833_);
if (v___x_835_ == 0)
{
return v___x_834_;
}
else
{
uint8_t v___x_836_; 
v___x_836_ = lean_nat_dec_le(v___x_833_, v___x_833_);
if (v___x_836_ == 0)
{
if (v___x_835_ == 0)
{
return v___x_834_;
}
else
{
size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; 
v___x_837_ = ((size_t)0ULL);
v___x_838_ = lean_usize_of_nat(v___x_833_);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_825_, v_tail_830_, v___x_837_, v___x_838_, v___x_834_, v___y_827_);
return v___x_839_;
}
}
else
{
size_t v___x_840_; size_t v___x_841_; lean_object* v___x_842_; 
v___x_840_ = ((size_t)0ULL);
v___x_841_ = lean_usize_of_nat(v___x_833_);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_825_, v_tail_830_, v___x_840_, v___x_841_, v___x_834_, v___y_827_);
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(lean_object* v_multigoals_843_, lean_object* v_t_844_, lean_object* v_start_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_nat_dec_eq(v_start_845_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v_root_850_; lean_object* v_tail_851_; size_t v_shift_852_; lean_object* v_tailOff_853_; uint8_t v___x_854_; 
v_root_850_ = lean_ctor_get(v_t_844_, 0);
v_tail_851_ = lean_ctor_get(v_t_844_, 1);
v_shift_852_ = lean_ctor_get_usize(v_t_844_, 4);
v_tailOff_853_ = lean_ctor_get(v_t_844_, 3);
v___x_854_ = lean_nat_dec_le(v_tailOff_853_, v_start_845_);
if (v___x_854_ == 0)
{
size_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_855_ = lean_usize_of_nat(v_start_845_);
v___x_856_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_843_, v_root_850_, v___x_855_, v_shift_852_, v___y_846_);
v___x_857_ = lean_array_get_size(v_tail_851_);
v___x_858_ = lean_box(0);
v___x_859_ = lean_nat_dec_lt(v___x_848_, v___x_857_);
if (v___x_859_ == 0)
{
return v___x_858_;
}
else
{
uint8_t v___x_860_; 
v___x_860_ = lean_nat_dec_le(v___x_857_, v___x_857_);
if (v___x_860_ == 0)
{
if (v___x_859_ == 0)
{
return v___x_858_;
}
else
{
size_t v___x_861_; size_t v___x_862_; lean_object* v___x_863_; 
v___x_861_ = ((size_t)0ULL);
v___x_862_ = lean_usize_of_nat(v___x_857_);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_843_, v_tail_851_, v___x_861_, v___x_862_, v___x_858_, v___y_846_);
return v___x_863_;
}
}
else
{
size_t v___x_864_; size_t v___x_865_; lean_object* v___x_866_; 
v___x_864_ = ((size_t)0ULL);
v___x_865_ = lean_usize_of_nat(v___x_857_);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_843_, v_tail_851_, v___x_864_, v___x_865_, v___x_858_, v___y_846_);
return v___x_866_;
}
}
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_867_ = lean_nat_sub(v_start_845_, v_tailOff_853_);
v___x_868_ = lean_array_get_size(v_tail_851_);
v___x_869_ = lean_box(0);
v___x_870_ = lean_nat_dec_lt(v___x_867_, v___x_868_);
if (v___x_870_ == 0)
{
lean_dec(v___x_867_);
return v___x_869_;
}
else
{
uint8_t v___x_871_; 
v___x_871_ = lean_nat_dec_le(v___x_868_, v___x_868_);
if (v___x_871_ == 0)
{
if (v___x_870_ == 0)
{
lean_dec(v___x_867_);
return v___x_869_;
}
else
{
size_t v___x_872_; size_t v___x_873_; lean_object* v___x_874_; 
v___x_872_ = lean_usize_of_nat(v___x_867_);
lean_dec(v___x_867_);
v___x_873_ = lean_usize_of_nat(v___x_868_);
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_843_, v_tail_851_, v___x_872_, v___x_873_, v___x_869_, v___y_846_);
return v___x_874_;
}
}
else
{
size_t v___x_875_; size_t v___x_876_; lean_object* v___x_877_; 
v___x_875_ = lean_usize_of_nat(v___x_867_);
lean_dec(v___x_867_);
v___x_876_ = lean_usize_of_nat(v___x_868_);
v___x_877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_843_, v_tail_851_, v___x_875_, v___x_876_, v___x_869_, v___y_846_);
return v___x_877_;
}
}
}
}
else
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_843_, v_t_844_, v___y_846_);
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___redArg(lean_object* v_multigoals_879_, lean_object* v_trees_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_879_, v_trees_880_, v___x_883_, v_a_881_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___redArg___boxed(lean_object* v_multigoals_885_, lean_object* v_trees_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_885_, v_trees_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_trees_886_);
lean_dec(v_multigoals_885_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg___boxed(lean_object* v_multigoals_890_, lean_object* v_as_891_, lean_object* v_i_892_, lean_object* v_stop_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
size_t v_i_boxed_897_; size_t v_stop_boxed_898_; lean_object* v_res_899_; 
v_i_boxed_897_ = lean_unbox_usize(v_i_892_);
lean_dec(v_i_892_);
v_stop_boxed_898_ = lean_unbox_usize(v_stop_893_);
lean_dec(v_stop_893_);
v_res_899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_890_, v_as_891_, v_i_boxed_897_, v_stop_boxed_898_, v_b_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v_as_891_);
lean_dec(v_multigoals_890_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_multigoals_900_, lean_object* v_as_901_, lean_object* v_i_902_, lean_object* v_stop_903_, lean_object* v_b_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
size_t v_i_boxed_907_; size_t v_stop_boxed_908_; lean_object* v_res_909_; 
v_i_boxed_907_ = lean_unbox_usize(v_i_902_);
lean_dec(v_i_902_);
v_stop_boxed_908_ = lean_unbox_usize(v_stop_903_);
lean_dec(v_stop_903_);
v_res_909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_900_, v_as_901_, v_i_boxed_907_, v_stop_boxed_908_, v_b_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v_as_901_);
lean_dec(v_multigoals_900_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg___boxed(lean_object* v_multigoals_910_, lean_object* v_t_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_910_, v_t_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v_t_911_);
lean_dec(v_multigoals_910_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_multigoals_915_, lean_object* v_x_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_915_, v_x_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v_x_916_);
lean_dec(v_multigoals_915_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg___boxed(lean_object* v_multigoals_920_, lean_object* v_t_921_, lean_object* v_start_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_920_, v_t_921_, v_start_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec(v_start_922_);
lean_dec_ref(v_t_921_);
lean_dec(v_multigoals_920_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___boxed(lean_object* v_multigoals_926_, lean_object* v_x_927_, lean_object* v_x_928_, lean_object* v_x_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
size_t v_x_10205__boxed_932_; size_t v_x_10206__boxed_933_; lean_object* v_res_934_; 
v_x_10205__boxed_932_ = lean_unbox_usize(v_x_928_);
lean_dec(v_x_928_);
v_x_10206__boxed_933_ = lean_unbox_usize(v_x_929_);
lean_dec(v_x_929_);
v_res_934_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_926_, v_x_927_, v_x_10205__boxed_932_, v_x_10206__boxed_933_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v_x_927_);
lean_dec(v_multigoals_926_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg___boxed(lean_object* v_multigoals_935_, lean_object* v_x_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg(v_multigoals_935_, v_x_936_, v_a_937_);
lean_dec(v_a_937_);
lean_dec(v_multigoals_935_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList(lean_object* v_multigoals_940_, lean_object* v_00_u03c9_941_, lean_object* v_trees_942_, lean_object* v_a_943_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_940_, v_trees_942_, v_a_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___boxed(lean_object* v_multigoals_946_, lean_object* v_00_u03c9_947_, lean_object* v_trees_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList(v_multigoals_946_, v_00_u03c9_947_, v_trees_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_trees_948_);
lean_dec(v_multigoals_946_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics(lean_object* v_multigoals_952_, lean_object* v_00_u03c9_953_, lean_object* v_x_954_, lean_object* v_a_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___redArg(v_multigoals_952_, v_x_954_, v_a_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics___boxed(lean_object* v_multigoals_958_, lean_object* v_00_u03c9_959_, lean_object* v_x_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics(v_multigoals_958_, v_00_u03c9_959_, v_x_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec(v_multigoals_958_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0(lean_object* v_00_u03c9_964_, lean_object* v_multigoals_965_, lean_object* v_t_966_, lean_object* v_start_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_965_, v_t_966_, v_start_967_, v___y_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0___boxed(lean_object* v_00_u03c9_971_, lean_object* v_multigoals_972_, lean_object* v_t_973_, lean_object* v_start_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0(v_00_u03c9_971_, v_multigoals_972_, v_t_973_, v_start_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec(v_start_974_);
lean_dec_ref(v_t_973_);
lean_dec(v_multigoals_972_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2(lean_object* v_00_u03b2_978_, lean_object* v_m_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v_m_979_, v_a_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2___boxed(lean_object* v_00_u03b2_982_, lean_object* v_m_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2(v_00_u03b2_982_, v_m_983_, v_a_984_);
lean_dec_ref(v_a_984_);
lean_dec_ref(v_m_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3(lean_object* v_00_u03b2_986_, lean_object* v_m_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v_m_987_, v_a_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3___boxed(lean_object* v_00_u03b2_990_, lean_object* v_m_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3(v_00_u03b2_990_, v_m_991_, v_a_992_);
lean_dec_ref(v_a_992_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4(lean_object* v_00_u03b2_994_, lean_object* v_m_995_, lean_object* v_a_996_, lean_object* v_b_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v_m_995_, v_a_996_, v_b_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0(lean_object* v_00_u03c9_999_, lean_object* v_multigoals_1000_, lean_object* v_x_1001_, size_t v_x_1002_, size_t v_x_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_1000_, v_x_1001_, v_x_1002_, v_x_1003_, v___y_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___boxed(lean_object* v_00_u03c9_1007_, lean_object* v_multigoals_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
size_t v_x_10720__boxed_1014_; size_t v_x_10721__boxed_1015_; lean_object* v_res_1016_; 
v_x_10720__boxed_1014_ = lean_unbox_usize(v_x_1010_);
lean_dec(v_x_1010_);
v_x_10721__boxed_1015_ = lean_unbox_usize(v_x_1011_);
lean_dec(v_x_1011_);
v_res_1016_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0(v_00_u03c9_1007_, v_multigoals_1008_, v_x_1009_, v_x_10720__boxed_1014_, v_x_10721__boxed_1015_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v_x_1009_);
lean_dec(v_multigoals_1008_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1(lean_object* v_00_u03c9_1017_, lean_object* v_multigoals_1018_, lean_object* v_as_1019_, size_t v_i_1020_, size_t v_stop_1021_, lean_object* v_b_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_1018_, v_as_1019_, v_i_1020_, v_stop_1021_, v_b_1022_, v___y_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___boxed(lean_object* v_00_u03c9_1026_, lean_object* v_multigoals_1027_, lean_object* v_as_1028_, lean_object* v_i_1029_, lean_object* v_stop_1030_, lean_object* v_b_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
size_t v_i_boxed_1034_; size_t v_stop_boxed_1035_; lean_object* v_res_1036_; 
v_i_boxed_1034_ = lean_unbox_usize(v_i_1029_);
lean_dec(v_i_1029_);
v_stop_boxed_1035_ = lean_unbox_usize(v_stop_1030_);
lean_dec(v_stop_1030_);
v_res_1036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1(v_00_u03c9_1026_, v_multigoals_1027_, v_as_1028_, v_i_boxed_1034_, v_stop_boxed_1035_, v_b_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v_as_1028_);
lean_dec(v_multigoals_1027_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2(lean_object* v_00_u03c9_1037_, lean_object* v_multigoals_1038_, lean_object* v_t_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_1038_, v_t_1039_, v___y_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___boxed(lean_object* v_00_u03c9_1043_, lean_object* v_multigoals_1044_, lean_object* v_t_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2(v_00_u03c9_1043_, v_multigoals_1044_, v_t_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v_t_1045_);
lean_dec(v_multigoals_1044_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5(lean_object* v_00_u03b2_1049_, lean_object* v_a_1050_, lean_object* v_x_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_a_1050_, v_x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1053_, lean_object* v_a_1054_, lean_object* v_x_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5(v_00_u03b2_1053_, v_a_1054_, v_x_1055_);
lean_dec(v_x_1055_);
lean_dec_ref(v_a_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7(lean_object* v_00_u03b2_1057_, lean_object* v_a_1058_, lean_object* v_x_1059_){
_start:
{
uint8_t v___x_1060_; 
v___x_1060_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_1058_, v_x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1061_, lean_object* v_a_1062_, lean_object* v_x_1063_){
_start:
{
uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7(v_00_u03b2_1061_, v_a_1062_, v_x_1063_);
lean_dec(v_x_1063_);
lean_dec_ref(v_a_1062_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8(lean_object* v_00_u03b2_1066_, lean_object* v_a_1067_, lean_object* v_x_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_1067_, v_x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___boxed(lean_object* v_00_u03b2_1070_, lean_object* v_a_1071_, lean_object* v_x_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8(v_00_u03b2_1070_, v_a_1071_, v_x_1072_);
lean_dec_ref(v_a_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10(lean_object* v_00_u03b2_1074_, lean_object* v_data_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10___redArg(v_data_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11(lean_object* v_00_u03b2_1077_, lean_object* v_a_1078_, lean_object* v_b_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(v_a_1078_, v_b_1079_, v_x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2(lean_object* v_00_u03c9_1082_, lean_object* v_multigoals_1083_, lean_object* v_x_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_1083_, v_x_1084_, v___y_1085_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c9_1088_, lean_object* v_multigoals_1089_, lean_object* v_x_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2(v_00_u03c9_1088_, v_multigoals_1089_, v_x_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v_x_1090_);
lean_dec(v_multigoals_1089_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3(lean_object* v_00_u03c9_1094_, lean_object* v_multigoals_1095_, lean_object* v_as_1096_, size_t v_i_1097_, size_t v_stop_1098_, lean_object* v_b_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_1095_, v_as_1096_, v_i_1097_, v_stop_1098_, v_b_1099_, v___y_1100_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03c9_1103_, lean_object* v_multigoals_1104_, lean_object* v_as_1105_, lean_object* v_i_1106_, lean_object* v_stop_1107_, lean_object* v_b_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
size_t v_i_boxed_1111_; size_t v_stop_boxed_1112_; lean_object* v_res_1113_; 
v_i_boxed_1111_ = lean_unbox_usize(v_i_1106_);
lean_dec(v_i_1106_);
v_stop_boxed_1112_ = lean_unbox_usize(v_stop_1107_);
lean_dec(v_stop_1107_);
v_res_1113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3(v_00_u03c9_1103_, v_multigoals_1104_, v_as_1105_, v_i_boxed_1111_, v_stop_boxed_1112_, v_b_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v_as_1105_);
lean_dec(v_multigoals_1104_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13(lean_object* v_00_u03b2_1114_, lean_object* v_i_1115_, lean_object* v_source_1116_, lean_object* v_target_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13___redArg(v_i_1115_, v_source_1116_, v_target_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14(lean_object* v_00_u03b2_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14___redArg(v_x_1120_, v_x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__0(lean_object* v_a_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_nat_to_int(v_a_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v_infoState_1128_; lean_object* v_trees_1129_; lean_object* v___x_1130_; 
v___x_1127_ = lean_st_ref_get(v___y_1125_);
v_infoState_1128_ = lean_ctor_get(v___x_1127_, 8);
lean_inc_ref(v_infoState_1128_);
lean_dec(v___x_1127_);
v_trees_1129_ = lean_ctor_get(v_infoState_1128_, 2);
lean_inc_ref(v_trees_1129_);
lean_dec_ref(v_infoState_1128_);
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_trees_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg___boxed(lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_1131_);
lean_dec(v___y_1131_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3(lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___boxed(lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3(v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1141_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = lean_box(0);
v___x_1143_ = lean_unsigned_to_nat(16u);
v___x_1144_ = lean_mk_array(v___x_1143_, v___x_1142_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0);
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v___x_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0(lean_object* v_stx_1148_, lean_object* v_val_1149_, lean_object* v_a_1150_, lean_object* v_x_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1153_ = lean_obj_once(&l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1, &l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1_once, _init_l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1);
v___x_1154_ = lean_st_mk_ref(v___x_1153_);
v___x_1155_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_getTactics___redArg(v_stx_1148_, v___x_1154_);
v___x_1156_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_val_1149_, v_a_1150_, v___x_1154_);
v___x_1157_ = lean_st_ref_get(v___x_1154_);
lean_dec(v___x_1154_);
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___boxed(lean_object* v_stx_1159_, lean_object* v_val_1160_, lean_object* v_a_1161_, lean_object* v_x_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0(v_stx_1159_, v_val_1160_, v_a_1161_, v_x_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_val_1160_);
return v_res_1164_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__11(lean_object* v_opts_1165_, lean_object* v_opt_1166_){
_start:
{
lean_object* v_name_1167_; lean_object* v_defValue_1168_; lean_object* v_map_1169_; lean_object* v___x_1170_; 
v_name_1167_ = lean_ctor_get(v_opt_1166_, 0);
v_defValue_1168_ = lean_ctor_get(v_opt_1166_, 1);
v_map_1169_ = lean_ctor_get(v_opts_1165_, 0);
v___x_1170_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1169_, v_name_1167_);
if (lean_obj_tag(v___x_1170_) == 0)
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_unbox(v_defValue_1168_);
return v___x_1171_;
}
else
{
lean_object* v_val_1172_; 
v_val_1172_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_val_1172_);
lean_dec_ref(v___x_1170_);
if (lean_obj_tag(v_val_1172_) == 1)
{
uint8_t v_v_1173_; 
v_v_1173_ = lean_ctor_get_uint8(v_val_1172_, 0);
lean_dec_ref(v_val_1172_);
return v_v_1173_;
}
else
{
uint8_t v___x_1174_; 
lean_dec(v_val_1172_);
v___x_1174_ = lean_unbox(v_defValue_1168_);
return v___x_1174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__11___boxed(lean_object* v_opts_1175_, lean_object* v_opt_1176_){
_start:
{
uint8_t v_res_1177_; lean_object* v_r_1178_; 
v_res_1177_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__11(v_opts_1175_, v_opt_1176_);
lean_dec_ref(v_opt_1176_);
lean_dec_ref(v_opts_1175_);
v_r_1178_ = lean_box(v_res_1177_);
return v_r_1178_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__0);
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__1);
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
lean_ctor_set(v___x_1184_, 2, v___x_1183_);
lean_ctor_set(v___x_1184_, 3, v___x_1183_);
lean_ctor_set(v___x_1184_, 4, v___x_1182_);
lean_ctor_set(v___x_1184_, 5, v___x_1182_);
lean_ctor_set(v___x_1184_, 6, v___x_1182_);
lean_ctor_set(v___x_1184_, 7, v___x_1182_);
lean_ctor_set(v___x_1184_, 8, v___x_1182_);
lean_ctor_set(v___x_1184_, 9, v___x_1182_);
return v___x_1184_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_unsigned_to_nat(32u);
v___x_1186_ = lean_mk_empty_array_with_capacity(v___x_1185_);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1188_ = ((size_t)5ULL);
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = lean_unsigned_to_nat(32u);
v___x_1191_ = lean_mk_empty_array_with_capacity(v___x_1190_);
v___x_1192_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__3);
v___x_1193_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___x_1191_);
lean_ctor_set(v___x_1193_, 2, v___x_1189_);
lean_ctor_set(v___x_1193_, 3, v___x_1189_);
lean_ctor_set_usize(v___x_1193_, 4, v___x_1188_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1194_ = lean_box(1);
v___x_1195_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__4);
v___x_1196_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__1);
v___x_1197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1195_);
lean_ctor_set(v___x_1197_, 2, v___x_1194_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg(lean_object* v_msgData_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; lean_object* v_env_1202_; lean_object* v___x_1203_; lean_object* v_scopes_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v_opts_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1201_ = lean_st_ref_get(v___y_1199_);
v_env_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc_ref(v_env_1202_);
lean_dec(v___x_1201_);
v___x_1203_ = lean_st_ref_get(v___y_1199_);
v_scopes_1204_ = lean_ctor_get(v___x_1203_, 2);
lean_inc(v_scopes_1204_);
lean_dec(v___x_1203_);
v___x_1205_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1206_ = l_List_head_x21___redArg(v___x_1205_, v_scopes_1204_);
lean_dec(v_scopes_1204_);
v_opts_1207_ = lean_ctor_get(v___x_1206_, 1);
lean_inc_ref(v_opts_1207_);
lean_dec(v___x_1206_);
v___x_1208_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__2);
v___x_1209_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___closed__5);
v___x_1210_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1210_, 0, v_env_1202_);
lean_ctor_set(v___x_1210_, 1, v___x_1208_);
lean_ctor_set(v___x_1210_, 2, v___x_1209_);
lean_ctor_set(v___x_1210_, 3, v_opts_1207_);
v___x_1211_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v_msgData_1198_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_msgData_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg(v_msgData_1213_, v___y_1214_);
lean_dec(v___y_1214_);
return v_res_1216_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___lam__0(uint8_t v___y_1218_, uint8_t v_suppressElabErrors_1219_, lean_object* v_x_1220_){
_start:
{
if (lean_obj_tag(v_x_1220_) == 1)
{
lean_object* v_pre_1221_; 
v_pre_1221_ = lean_ctor_get(v_x_1220_, 0);
if (lean_obj_tag(v_pre_1221_) == 0)
{
lean_object* v_str_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v_str_1222_ = lean_ctor_get(v_x_1220_, 1);
v___x_1223_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___lam__0___closed__0));
v___x_1224_ = lean_string_dec_eq(v_str_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
return v___y_1218_;
}
else
{
return v_suppressElabErrors_1219_;
}
}
else
{
return v___y_1218_;
}
}
else
{
return v___y_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___lam__0___boxed(lean_object* v___y_1225_, lean_object* v_suppressElabErrors_1226_, lean_object* v_x_1227_){
_start:
{
uint8_t v___y_8611__boxed_1228_; uint8_t v_suppressElabErrors_boxed_1229_; uint8_t v_res_1230_; lean_object* v_r_1231_; 
v___y_8611__boxed_1228_ = lean_unbox(v___y_1225_);
v_suppressElabErrors_boxed_1229_ = lean_unbox(v_suppressElabErrors_1226_);
v_res_1230_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___lam__0(v___y_8611__boxed_1228_, v_suppressElabErrors_boxed_1229_, v_x_1227_);
lean_dec(v_x_1227_);
v_r_1231_ = lean_box(v_res_1230_);
return v_r_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(lean_object* v_ref_1233_, lean_object* v_msgData_1234_, uint8_t v_severity_1235_, uint8_t v_isSilent_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; uint8_t v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; uint8_t v___y_1304_; uint8_t v___y_1305_; lean_object* v___y_1306_; uint8_t v___y_1307_; lean_object* v___y_1308_; uint8_t v___y_1332_; lean_object* v___y_1333_; uint8_t v___y_1334_; uint8_t v___y_1335_; lean_object* v___y_1336_; uint8_t v___y_1340_; uint8_t v___y_1341_; uint8_t v___y_1342_; uint8_t v___x_1357_; uint8_t v___y_1359_; uint8_t v___y_1360_; uint8_t v___y_1361_; uint8_t v___y_1363_; uint8_t v___x_1375_; 
v___x_1357_ = 2;
v___x_1375_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1235_, v___x_1357_);
if (v___x_1375_ == 0)
{
v___y_1363_ = v___x_1375_;
goto v___jp_1362_;
}
else
{
uint8_t v___x_1376_; 
lean_inc_ref(v_msgData_1234_);
v___x_1376_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1234_);
v___y_1363_ = v___x_1376_;
goto v___jp_1362_;
}
v___jp_1240_:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Elab_Command_getScope___redArg(v___y_1248_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1251_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref(v___x_1249_);
v___x_1251_ = l_Lean_Elab_Command_getScope___redArg(v___y_1248_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1286_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1286_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1286_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v_currNamespace_1257_; lean_object* v_openDecls_1258_; lean_object* v_env_1259_; lean_object* v_messages_1260_; lean_object* v_scopes_1261_; lean_object* v_usedQuotCtxts_1262_; lean_object* v_nextMacroScope_1263_; lean_object* v_maxRecDepth_1264_; lean_object* v_ngen_1265_; lean_object* v_auxDeclNGen_1266_; lean_object* v_infoState_1267_; lean_object* v_traceState_1268_; lean_object* v_snapshotTasks_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1285_; 
v___x_1256_ = lean_st_ref_take(v___y_1248_);
v_currNamespace_1257_ = lean_ctor_get(v_a_1250_, 2);
lean_inc(v_currNamespace_1257_);
lean_dec(v_a_1250_);
v_openDecls_1258_ = lean_ctor_get(v_a_1252_, 3);
lean_inc(v_openDecls_1258_);
lean_dec(v_a_1252_);
v_env_1259_ = lean_ctor_get(v___x_1256_, 0);
v_messages_1260_ = lean_ctor_get(v___x_1256_, 1);
v_scopes_1261_ = lean_ctor_get(v___x_1256_, 2);
v_usedQuotCtxts_1262_ = lean_ctor_get(v___x_1256_, 3);
v_nextMacroScope_1263_ = lean_ctor_get(v___x_1256_, 4);
v_maxRecDepth_1264_ = lean_ctor_get(v___x_1256_, 5);
v_ngen_1265_ = lean_ctor_get(v___x_1256_, 6);
v_auxDeclNGen_1266_ = lean_ctor_get(v___x_1256_, 7);
v_infoState_1267_ = lean_ctor_get(v___x_1256_, 8);
v_traceState_1268_ = lean_ctor_get(v___x_1256_, 9);
v_snapshotTasks_1269_ = lean_ctor_get(v___x_1256_, 10);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1271_ = v___x_1256_;
v_isShared_1272_ = v_isSharedCheck_1285_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_snapshotTasks_1269_);
lean_inc(v_traceState_1268_);
lean_inc(v_infoState_1267_);
lean_inc(v_auxDeclNGen_1266_);
lean_inc(v_ngen_1265_);
lean_inc(v_maxRecDepth_1264_);
lean_inc(v_nextMacroScope_1263_);
lean_inc(v_usedQuotCtxts_1262_);
lean_inc(v_scopes_1261_);
lean_inc(v_messages_1260_);
lean_inc(v_env_1259_);
lean_dec(v___x_1256_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1285_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v_currNamespace_1257_);
lean_ctor_set(v___x_1273_, 1, v_openDecls_1258_);
v___x_1274_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v___y_1247_);
lean_inc_ref(v___y_1242_);
lean_inc_ref(v___y_1245_);
v___x_1275_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1275_, 0, v___y_1245_);
lean_ctor_set(v___x_1275_, 1, v___y_1243_);
lean_ctor_set(v___x_1275_, 2, v___y_1246_);
lean_ctor_set(v___x_1275_, 3, v___y_1242_);
lean_ctor_set(v___x_1275_, 4, v___x_1274_);
lean_ctor_set_uint8(v___x_1275_, sizeof(void*)*5, v___y_1244_);
lean_ctor_set_uint8(v___x_1275_, sizeof(void*)*5 + 1, v___y_1241_);
lean_ctor_set_uint8(v___x_1275_, sizeof(void*)*5 + 2, v_isSilent_1236_);
v___x_1276_ = l_Lean_MessageLog_add(v___x_1275_, v_messages_1260_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v___x_1276_);
v___x_1278_ = v___x_1271_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_env_1259_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_scopes_1261_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_usedQuotCtxts_1262_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_nextMacroScope_1263_);
lean_ctor_set(v_reuseFailAlloc_1284_, 5, v_maxRecDepth_1264_);
lean_ctor_set(v_reuseFailAlloc_1284_, 6, v_ngen_1265_);
lean_ctor_set(v_reuseFailAlloc_1284_, 7, v_auxDeclNGen_1266_);
lean_ctor_set(v_reuseFailAlloc_1284_, 8, v_infoState_1267_);
lean_ctor_set(v_reuseFailAlloc_1284_, 9, v_traceState_1268_);
lean_ctor_set(v_reuseFailAlloc_1284_, 10, v_snapshotTasks_1269_);
v___x_1278_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1279_ = lean_st_ref_set(v___y_1248_, v___x_1278_);
v___x_1280_ = lean_box(0);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v___x_1280_);
v___x_1282_ = v___x_1254_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_a_1250_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1243_);
v_a_1287_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1251_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1251_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1243_);
v_a_1295_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1249_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1249_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
v___jp_1303_:
{
lean_object* v_fileName_1309_; lean_object* v_fileMap_1310_; uint8_t v_suppressElabErrors_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1330_; 
v_fileName_1309_ = lean_ctor_get(v___y_1237_, 0);
v_fileMap_1310_ = lean_ctor_get(v___y_1237_, 1);
v_suppressElabErrors_1311_ = lean_ctor_get_uint8(v___y_1237_, sizeof(void*)*10);
v___x_1312_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1234_);
v___x_1313_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg(v___x_1312_, v___y_1238_);
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1330_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1330_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_inc_ref_n(v_fileMap_1310_, 2);
v___x_1318_ = l_Lean_FileMap_toPosition(v_fileMap_1310_, v___y_1306_);
lean_dec(v___y_1306_);
v___x_1319_ = l_Lean_FileMap_toPosition(v_fileMap_1310_, v___y_1308_);
lean_dec(v___y_1308_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
v___x_1321_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___closed__0));
if (v_suppressElabErrors_1311_ == 0)
{
lean_del_object(v___x_1316_);
v___y_1241_ = v___y_1305_;
v___y_1242_ = v___x_1321_;
v___y_1243_ = v___x_1318_;
v___y_1244_ = v___y_1307_;
v___y_1245_ = v_fileName_1309_;
v___y_1246_ = v___x_1320_;
v___y_1247_ = v_a_1314_;
v___y_1248_ = v___y_1238_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___f_1324_; uint8_t v___x_1325_; 
v___x_1322_ = lean_box(v___y_1304_);
v___x_1323_ = lean_box(v_suppressElabErrors_1311_);
v___f_1324_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1324_, 0, v___x_1322_);
lean_closure_set(v___f_1324_, 1, v___x_1323_);
lean_inc(v_a_1314_);
v___x_1325_ = l_Lean_MessageData_hasTag(v___f_1324_, v_a_1314_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
lean_dec_ref(v___x_1320_);
lean_dec_ref(v___x_1318_);
lean_dec(v_a_1314_);
v___x_1326_ = lean_box(0);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1326_);
v___x_1328_ = v___x_1316_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
else
{
lean_del_object(v___x_1316_);
v___y_1241_ = v___y_1305_;
v___y_1242_ = v___x_1321_;
v___y_1243_ = v___x_1318_;
v___y_1244_ = v___y_1307_;
v___y_1245_ = v_fileName_1309_;
v___y_1246_ = v___x_1320_;
v___y_1247_ = v_a_1314_;
v___y_1248_ = v___y_1238_;
goto v___jp_1240_;
}
}
}
}
v___jp_1331_:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_Syntax_getTailPos_x3f(v___y_1333_, v___y_1335_);
lean_dec(v___y_1333_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_inc(v___y_1336_);
v___y_1304_ = v___y_1332_;
v___y_1305_ = v___y_1334_;
v___y_1306_ = v___y_1336_;
v___y_1307_ = v___y_1335_;
v___y_1308_ = v___y_1336_;
goto v___jp_1303_;
}
else
{
lean_object* v_val_1338_; 
v_val_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_val_1338_);
lean_dec_ref(v___x_1337_);
v___y_1304_ = v___y_1332_;
v___y_1305_ = v___y_1334_;
v___y_1306_ = v___y_1336_;
v___y_1307_ = v___y_1335_;
v___y_1308_ = v_val_1338_;
goto v___jp_1303_;
}
}
v___jp_1339_:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_Elab_Command_getRef___redArg(v___y_1237_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v_ref_1345_; lean_object* v___x_1346_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref(v___x_1343_);
v_ref_1345_ = l_Lean_replaceRef(v_ref_1233_, v_a_1344_);
lean_dec(v_a_1344_);
v___x_1346_ = l_Lean_Syntax_getPos_x3f(v_ref_1345_, v___y_1341_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_unsigned_to_nat(0u);
v___y_1332_ = v___y_1340_;
v___y_1333_ = v_ref_1345_;
v___y_1334_ = v___y_1342_;
v___y_1335_ = v___y_1341_;
v___y_1336_ = v___x_1347_;
goto v___jp_1331_;
}
else
{
lean_object* v_val_1348_; 
v_val_1348_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_val_1348_);
lean_dec_ref(v___x_1346_);
v___y_1332_ = v___y_1340_;
v___y_1333_ = v_ref_1345_;
v___y_1334_ = v___y_1342_;
v___y_1335_ = v___y_1341_;
v___y_1336_ = v_val_1348_;
goto v___jp_1331_;
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec_ref(v_msgData_1234_);
v_a_1349_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1343_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1343_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
v___jp_1358_:
{
if (v___y_1361_ == 0)
{
v___y_1340_ = v___y_1359_;
v___y_1341_ = v___y_1360_;
v___y_1342_ = v_severity_1235_;
goto v___jp_1339_;
}
else
{
v___y_1340_ = v___y_1359_;
v___y_1341_ = v___y_1360_;
v___y_1342_ = v___x_1357_;
goto v___jp_1339_;
}
}
v___jp_1362_:
{
if (v___y_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v_scopes_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_opts_1368_; uint8_t v___x_1369_; uint8_t v___x_1370_; 
v___x_1364_ = lean_st_ref_get(v___y_1238_);
v_scopes_1365_ = lean_ctor_get(v___x_1364_, 2);
lean_inc(v_scopes_1365_);
lean_dec(v___x_1364_);
v___x_1366_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1367_ = l_List_head_x21___redArg(v___x_1366_, v_scopes_1365_);
lean_dec(v_scopes_1365_);
v_opts_1368_ = lean_ctor_get(v___x_1367_, 1);
lean_inc_ref(v_opts_1368_);
lean_dec(v___x_1367_);
v___x_1369_ = 1;
v___x_1370_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1235_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_dec_ref(v_opts_1368_);
v___y_1359_ = v___y_1363_;
v___y_1360_ = v___y_1363_;
v___y_1361_ = v___x_1370_;
goto v___jp_1358_;
}
else
{
lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1371_ = l_Lean_warningAsError;
v___x_1372_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__11(v_opts_1368_, v___x_1371_);
lean_dec_ref(v_opts_1368_);
v___y_1359_ = v___y_1363_;
v___y_1360_ = v___y_1363_;
v___y_1361_ = v___x_1372_;
goto v___jp_1358_;
}
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_dec_ref(v_msgData_1234_);
v___x_1373_ = lean_box(0);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___boxed(lean_object* v_ref_1377_, lean_object* v_msgData_1378_, lean_object* v_severity_1379_, lean_object* v_isSilent_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v_severity_boxed_1384_; uint8_t v_isSilent_boxed_1385_; lean_object* v_res_1386_; 
v_severity_boxed_1384_ = lean_unbox(v_severity_1379_);
v_isSilent_boxed_1385_ = lean_unbox(v_isSilent_1380_);
v_res_1386_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(v_ref_1377_, v_msgData_1378_, v_severity_boxed_1384_, v_isSilent_boxed_1385_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v_ref_1377_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(lean_object* v_ref_1387_, lean_object* v_msgData_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v___x_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = 1;
v___x_1393_ = 0;
v___x_1394_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(v_ref_1387_, v_msgData_1388_, v___x_1392_, v___x_1393_, v___y_1389_, v___y_1390_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___boxed(lean_object* v_ref_1395_, lean_object* v_msgData_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(v_ref_1395_, v_msgData_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v_ref_1395_);
return v_res_1400_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__0));
v___x_1403_ = l_Lean_stringToMessageData(v___x_1402_);
return v___x_1403_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__2));
v___x_1406_ = l_Lean_stringToMessageData(v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(lean_object* v_linterOption_1407_, lean_object* v_stx_1408_, lean_object* v_msg_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_name_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1428_; 
v_name_1413_ = lean_ctor_get(v_linterOption_1407_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_linterOption_1407_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v_linterOption_1407_, 1);
lean_dec(v_unused_1429_);
v___x_1415_ = v_linterOption_1407_;
v_isShared_1416_ = v_isSharedCheck_1428_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_name_1413_);
lean_dec(v_linterOption_1407_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1428_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1417_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__1);
lean_inc(v_name_1413_);
v___x_1418_ = l_Lean_MessageData_ofName(v_name_1413_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set_tag(v___x_1415_, 7);
lean_ctor_set(v___x_1415_, 1, v___x_1418_);
lean_ctor_set(v___x_1415_, 0, v___x_1417_);
v___x_1420_ = v___x_1415_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v_disable_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1421_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___closed__3);
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v_disable_1423_ = l_Lean_MessageData_note(v___x_1422_);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v_msg_1409_);
lean_ctor_set(v___x_1424_, 1, v_disable_1423_);
v___x_1425_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1425_, 0, v_name_1413_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
v___x_1426_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(v_stx_1408_, v___x_1425_, v___y_1410_, v___y_1411_);
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___boxed(lean_object* v_linterOption_1430_, lean_object* v_stx_1431_, lean_object* v_msg_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(v_linterOption_1430_, v_stx_1431_, v_msg_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v_stx_1431_);
return v_res_1436_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__1));
v___x_1441_ = l_Lean_MessageData_ofFormat(v___x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(lean_object* v_as_1442_, size_t v_sz_1443_, size_t v_i_1444_, lean_object* v_b_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_a_1450_; uint8_t v___x_1454_; 
v___x_1454_ = lean_usize_dec_lt(v_i_1444_, v_sz_1443_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v_b_1445_);
return v___x_1455_;
}
else
{
lean_object* v_a_1456_; lean_object* v_fst_1457_; lean_object* v_snd_1458_; lean_object* v_start_1459_; lean_object* v_stop_1460_; lean_object* v_start_1461_; lean_object* v_stop_1462_; lean_object* v___x_1463_; uint8_t v___y_1465_; uint8_t v___x_1476_; 
v_a_1456_ = lean_array_uget_borrowed(v_as_1442_, v_i_1444_);
v_fst_1457_ = lean_ctor_get(v_a_1456_, 0);
v_snd_1458_ = lean_ctor_get(v_a_1456_, 1);
v_start_1459_ = lean_ctor_get(v_b_1445_, 0);
v_stop_1460_ = lean_ctor_get(v_b_1445_, 1);
v_start_1461_ = lean_ctor_get(v_fst_1457_, 0);
v_stop_1462_ = lean_ctor_get(v_fst_1457_, 1);
v___x_1463_ = l_Lean_Linter_Clippy_linter_clippy_unnecessarySeqFocus;
v___x_1476_ = lean_nat_dec_le(v_start_1459_, v_start_1461_);
if (v___x_1476_ == 0)
{
v___y_1465_ = v___x_1476_;
goto v___jp_1464_;
}
else
{
uint8_t v___x_1477_; 
v___x_1477_ = lean_nat_dec_le(v_stop_1462_, v_stop_1460_);
v___y_1465_ = v___x_1477_;
goto v___jp_1464_;
}
v___jp_1464_:
{
if (v___y_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec_ref(v_b_1445_);
v___x_1466_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2);
v___x_1467_ = l_Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(v___x_1463_, v_snd_1458_, v___x_1466_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_dec_ref(v___x_1467_);
lean_inc(v_fst_1457_);
v_a_1450_ = v_fst_1457_;
goto v___jp_1449_;
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1467_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
v_a_1450_ = v_b_1445_;
goto v___jp_1449_;
}
}
}
v___jp_1449_:
{
size_t v___x_1451_; size_t v___x_1452_; 
v___x_1451_ = ((size_t)1ULL);
v___x_1452_ = lean_usize_add(v_i_1444_, v___x_1451_);
v_i_1444_ = v___x_1452_;
v_b_1445_ = v_a_1450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___boxed(lean_object* v_as_1478_, lean_object* v_sz_1479_, lean_object* v_i_1480_, lean_object* v_b_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
size_t v_sz_boxed_1485_; size_t v_i_boxed_1486_; lean_object* v_res_1487_; 
v_sz_boxed_1485_ = lean_unbox_usize(v_sz_1479_);
lean_dec(v_sz_1479_);
v_i_boxed_1486_ = lean_unbox_usize(v_i_1480_);
lean_dec(v_i_1480_);
v_res_1487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(v_as_1478_, v_sz_boxed_1485_, v_i_boxed_1486_, v_b_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec_ref(v_as_1478_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(uint8_t v___x_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_){
_start:
{
if (lean_obj_tag(v_x_1490_) == 0)
{
return v_x_1489_;
}
else
{
lean_object* v_value_1491_; uint8_t v_used_1492_; 
v_value_1491_ = lean_ctor_get(v_x_1490_, 1);
v_used_1492_ = lean_ctor_get_uint8(v_value_1491_, sizeof(void*)*1);
if (v_used_1492_ == 0)
{
lean_object* v_tail_1493_; 
v_tail_1493_ = lean_ctor_get(v_x_1490_, 2);
lean_inc(v_tail_1493_);
lean_dec_ref(v_x_1490_);
v_x_1490_ = v_tail_1493_;
goto _start;
}
else
{
lean_object* v_key_1495_; lean_object* v_tail_1496_; lean_object* v_stx_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___y_1501_; lean_object* v___x_1505_; 
lean_inc(v_value_1491_);
v_key_1495_ = lean_ctor_get(v_x_1490_, 0);
lean_inc(v_key_1495_);
v_tail_1496_ = lean_ctor_get(v_x_1490_, 2);
lean_inc(v_tail_1496_);
lean_dec_ref(v_x_1490_);
v_stx_1497_ = lean_ctor_get(v_value_1491_, 0);
lean_inc(v_stx_1497_);
lean_dec(v_value_1491_);
v___x_1498_ = lean_unsigned_to_nat(1u);
v___x_1499_ = l_Lean_Syntax_getArg(v_stx_1497_, v___x_1498_);
lean_dec(v_stx_1497_);
v___x_1505_ = l_Lean_Syntax_getRange_x3f(v___x_1499_, v___x_1488_);
if (lean_obj_tag(v___x_1505_) == 0)
{
v___y_1501_ = v_key_1495_;
goto v___jp_1500_;
}
else
{
lean_object* v_val_1506_; 
lean_dec(v_key_1495_);
v_val_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_val_1506_);
lean_dec_ref(v___x_1505_);
v___y_1501_ = v_val_1506_;
goto v___jp_1500_;
}
v___jp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___y_1501_);
lean_ctor_set(v___x_1502_, 1, v___x_1499_);
v___x_1503_ = lean_array_push(v_x_1489_, v___x_1502_);
v_x_1489_ = v___x_1503_;
v_x_1490_ = v_tail_1496_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___boxed(lean_object* v___x_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_){
_start:
{
uint8_t v___x_9024__boxed_1510_; lean_object* v_res_1511_; 
v___x_9024__boxed_1510_ = lean_unbox(v___x_1507_);
v_res_1511_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(v___x_9024__boxed_1510_, v_x_1508_, v_x_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(uint8_t v___x_1512_, lean_object* v_as_1513_, size_t v_i_1514_, size_t v_stop_1515_, lean_object* v_b_1516_){
_start:
{
uint8_t v___x_1517_; 
v___x_1517_ = lean_usize_dec_eq(v_i_1514_, v_stop_1515_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; size_t v___x_1520_; size_t v___x_1521_; 
v___x_1518_ = lean_array_uget_borrowed(v_as_1513_, v_i_1514_);
lean_inc(v___x_1518_);
v___x_1519_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(v___x_1512_, v_b_1516_, v___x_1518_);
v___x_1520_ = ((size_t)1ULL);
v___x_1521_ = lean_usize_add(v_i_1514_, v___x_1520_);
v_i_1514_ = v___x_1521_;
v_b_1516_ = v___x_1519_;
goto _start;
}
else
{
return v_b_1516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7___boxed(lean_object* v___x_1523_, lean_object* v_as_1524_, lean_object* v_i_1525_, lean_object* v_stop_1526_, lean_object* v_b_1527_){
_start:
{
uint8_t v___x_9065__boxed_1528_; size_t v_i_boxed_1529_; size_t v_stop_boxed_1530_; lean_object* v_res_1531_; 
v___x_9065__boxed_1528_ = lean_unbox(v___x_1523_);
v_i_boxed_1529_ = lean_unbox_usize(v_i_1525_);
lean_dec(v_i_1525_);
v_stop_boxed_1530_ = lean_unbox_usize(v_stop_1526_);
lean_dec(v_stop_1526_);
v_res_1531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(v___x_9065__boxed_1528_, v_as_1524_, v_i_boxed_1529_, v_stop_boxed_1530_, v_b_1527_);
lean_dec_ref(v_as_1524_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(lean_object* v_o_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; lean_object* v_env_1536_; lean_object* v___x_1537_; lean_object* v_toEnvExtension_1538_; lean_object* v_asyncMode_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v_linterSets_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1535_ = lean_st_ref_get(v___y_1533_);
v_env_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc_ref(v_env_1536_);
lean_dec(v___x_1535_);
v___x_1537_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1538_ = lean_ctor_get(v___x_1537_, 0);
v_asyncMode_1539_ = lean_ctor_get(v_toEnvExtension_1538_, 2);
v___x_1540_ = lean_box(1);
v___x_1541_ = lean_box(0);
v_linterSets_1542_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1540_, v___x_1537_, v_env_1536_, v_asyncMode_1539_, v___x_1541_);
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v_o_1532_);
lean_ctor_set(v___x_1543_, 1, v_linterSets_1542_);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg___boxed(lean_object* v_o_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_o_1545_, v___y_1546_);
lean_dec(v___y_1546_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v_scopes_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v_opts_1556_; lean_object* v___x_1557_; 
v___x_1552_ = lean_st_ref_get(v___y_1550_);
v_scopes_1553_ = lean_ctor_get(v___x_1552_, 2);
lean_inc(v_scopes_1553_);
lean_dec(v___x_1552_);
v___x_1554_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1555_ = l_List_head_x21___redArg(v___x_1554_, v_scopes_1553_);
lean_dec(v_scopes_1553_);
v_opts_1556_ = lean_ctor_get(v___x_1555_, 1);
lean_inc_ref(v_opts_1556_);
lean_dec(v___x_1555_);
v___x_1557_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_opts_1556_, v___y_1550_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1___boxed(lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1561_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(lean_object* v___f_1564_, uint8_t v___x_1565_, lean_object* v_x1_1566_, lean_object* v_x2_1567_){
_start:
{
lean_object* v_fst_1568_; lean_object* v_fst_1569_; lean_object* v___f_1570_; lean_object* v___f_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_8422__overap_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v_fst_1568_ = lean_ctor_get(v_x1_1566_, 0);
lean_inc(v_fst_1568_);
lean_dec_ref(v_x1_1566_);
v_fst_1569_ = lean_ctor_get(v_x2_1567_, 0);
lean_inc(v_fst_1569_);
lean_dec_ref(v_x2_1567_);
v___f_1570_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___closed__0));
v___f_1571_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___closed__1));
lean_inc_ref(v___f_1564_);
v___x_1572_ = lean_apply_1(v___f_1564_, v_fst_1568_);
v___x_1573_ = lean_apply_1(v___f_1564_, v_fst_1569_);
v___x_8422__overap_1574_ = l_lexOrd___redArg(v___f_1570_, v___f_1571_);
v___x_1575_ = lean_apply_2(v___x_8422__overap_1574_, v___x_1572_, v___x_1573_);
v___x_1576_ = lean_unbox(v___x_1575_);
if (v___x_1576_ == 0)
{
return v___x_1565_;
}
else
{
uint8_t v___x_1577_; 
v___x_1577_ = 0;
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___boxed(lean_object* v___f_1578_, lean_object* v___x_1579_, lean_object* v_x1_1580_, lean_object* v_x2_1581_){
_start:
{
uint8_t v___x_9120__boxed_1582_; uint8_t v_res_1583_; lean_object* v_r_1584_; 
v___x_9120__boxed_1582_ = lean_unbox(v___x_1579_);
v_res_1583_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_1578_, v___x_9120__boxed_1582_, v_x1_1580_, v_x2_1581_);
v_r_1584_ = lean_box(v_res_1583_);
return v_r_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0(lean_object* v_r_1585_){
_start:
{
lean_object* v_start_1586_; lean_object* v_stop_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1596_; 
v_start_1586_ = lean_ctor_get(v_r_1585_, 0);
v_stop_1587_ = lean_ctor_get(v_r_1585_, 1);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_r_1585_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1589_ = v_r_1585_;
v_isShared_1590_ = v_isSharedCheck_1596_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_stop_1587_);
lean_inc(v_start_1586_);
lean_dec(v_r_1585_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1596_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1591_ = lean_nat_to_int(v_stop_1587_);
v___x_1592_ = lean_int_neg(v___x_1591_);
lean_dec(v___x_1591_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 1, v___x_1592_);
v___x_1594_ = v___x_1589_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_start_1586_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(lean_object* v_hi_1597_, lean_object* v_pivot_1598_, lean_object* v_as_1599_, lean_object* v_i_1600_, lean_object* v_k_1601_){
_start:
{
uint8_t v___x_1606_; 
v___x_1606_ = lean_nat_dec_lt(v_k_1601_, v_hi_1597_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec(v_k_1601_);
lean_dec_ref(v_pivot_1598_);
v___x_1607_ = lean_array_fswap(v_as_1599_, v_i_1600_, v_hi_1597_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v_i_1600_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
return v___x_1608_;
}
else
{
lean_object* v___x_1609_; lean_object* v_fst_1610_; lean_object* v_fst_1611_; lean_object* v___f_1612_; lean_object* v___f_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_8223__overap_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1609_ = lean_array_fget_borrowed(v_as_1599_, v_k_1601_);
v_fst_1610_ = lean_ctor_get(v___x_1609_, 0);
v_fst_1611_ = lean_ctor_get(v_pivot_1598_, 0);
v___f_1612_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___closed__0));
v___f_1613_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___closed__1));
lean_inc(v_fst_1610_);
v___x_1614_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0(v_fst_1610_);
lean_inc(v_fst_1611_);
v___x_1615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0(v_fst_1611_);
v___x_8223__overap_1616_ = l_lexOrd___redArg(v___f_1612_, v___f_1613_);
v___x_1617_ = lean_apply_2(v___x_8223__overap_1616_, v___x_1614_, v___x_1615_);
v___x_1618_ = lean_unbox(v___x_1617_);
if (v___x_1618_ == 0)
{
if (v___x_1606_ == 0)
{
goto v___jp_1602_;
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1619_ = lean_array_fswap(v_as_1599_, v_i_1600_, v_k_1601_);
v___x_1620_ = lean_unsigned_to_nat(1u);
v___x_1621_ = lean_nat_add(v_i_1600_, v___x_1620_);
lean_dec(v_i_1600_);
v___x_1622_ = lean_nat_add(v_k_1601_, v___x_1620_);
lean_dec(v_k_1601_);
v_as_1599_ = v___x_1619_;
v_i_1600_ = v___x_1621_;
v_k_1601_ = v___x_1622_;
goto _start;
}
}
else
{
goto v___jp_1602_;
}
}
v___jp_1602_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_unsigned_to_nat(1u);
v___x_1604_ = lean_nat_add(v_k_1601_, v___x_1603_);
lean_dec(v_k_1601_);
v_k_1601_ = v___x_1604_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___boxed(lean_object* v_hi_1624_, lean_object* v_pivot_1625_, lean_object* v_as_1626_, lean_object* v_i_1627_, lean_object* v_k_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(v_hi_1624_, v_pivot_1625_, v_as_1626_, v_i_1627_, v_k_1628_);
lean_dec(v_hi_1624_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(lean_object* v_n_1631_, lean_object* v_as_1632_, lean_object* v_lo_1633_, lean_object* v_hi_1634_){
_start:
{
lean_object* v___y_1636_; uint8_t v___x_1646_; 
v___x_1646_ = lean_nat_dec_lt(v_lo_1633_, v_hi_1634_);
if (v___x_1646_ == 0)
{
lean_dec(v_lo_1633_);
return v_as_1632_;
}
else
{
lean_object* v___f_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_mid_1650_; lean_object* v___y_1652_; lean_object* v___y_1658_; lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___f_1647_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___closed__0));
v___x_1648_ = lean_nat_add(v_lo_1633_, v_hi_1634_);
v___x_1649_ = lean_unsigned_to_nat(1u);
v_mid_1650_ = lean_nat_shiftr(v___x_1648_, v___x_1649_);
lean_dec(v___x_1648_);
v___x_1663_ = lean_array_fget_borrowed(v_as_1632_, v_mid_1650_);
v___x_1664_ = lean_array_fget_borrowed(v_as_1632_, v_lo_1633_);
lean_inc(v___x_1664_);
lean_inc(v___x_1663_);
v___x_1665_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_1647_, v___x_1646_, v___x_1663_, v___x_1664_);
if (v___x_1665_ == 0)
{
v___y_1658_ = v_as_1632_;
goto v___jp_1657_;
}
else
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_array_fswap(v_as_1632_, v_lo_1633_, v_mid_1650_);
v___y_1658_ = v___x_1666_;
goto v___jp_1657_;
}
v___jp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1653_ = lean_array_fget_borrowed(v___y_1652_, v_mid_1650_);
v___x_1654_ = lean_array_fget_borrowed(v___y_1652_, v_hi_1634_);
lean_inc(v___x_1654_);
lean_inc(v___x_1653_);
v___x_1655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_1647_, v___x_1646_, v___x_1653_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_dec(v_mid_1650_);
v___y_1636_ = v___y_1652_;
goto v___jp_1635_;
}
else
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_array_fswap(v___y_1652_, v_mid_1650_, v_hi_1634_);
lean_dec(v_mid_1650_);
v___y_1636_ = v___x_1656_;
goto v___jp_1635_;
}
}
v___jp_1657_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1659_ = lean_array_fget_borrowed(v___y_1658_, v_hi_1634_);
v___x_1660_ = lean_array_fget_borrowed(v___y_1658_, v_lo_1633_);
lean_inc(v___x_1660_);
lean_inc(v___x_1659_);
v___x_1661_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_1647_, v___x_1646_, v___x_1659_, v___x_1660_);
if (v___x_1661_ == 0)
{
v___y_1652_ = v___y_1658_;
goto v___jp_1651_;
}
else
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_array_fswap(v___y_1658_, v_lo_1633_, v_hi_1634_);
v___y_1652_ = v___x_1662_;
goto v___jp_1651_;
}
}
}
v___jp_1635_:
{
lean_object* v_pivot_1637_; lean_object* v___x_1638_; lean_object* v_fst_1639_; lean_object* v_snd_1640_; uint8_t v___x_1641_; 
v_pivot_1637_ = lean_array_fget(v___y_1636_, v_hi_1634_);
lean_inc_n(v_lo_1633_, 2);
v___x_1638_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(v_hi_1634_, v_pivot_1637_, v___y_1636_, v_lo_1633_, v_lo_1633_);
v_fst_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_fst_1639_);
v_snd_1640_ = lean_ctor_get(v___x_1638_, 1);
lean_inc(v_snd_1640_);
lean_dec_ref(v___x_1638_);
v___x_1641_ = lean_nat_dec_le(v_hi_1634_, v_fst_1639_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1642_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v_n_1631_, v_snd_1640_, v_lo_1633_, v_fst_1639_);
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = lean_nat_add(v_fst_1639_, v___x_1643_);
lean_dec(v_fst_1639_);
v_as_1632_ = v___x_1642_;
v_lo_1633_ = v___x_1644_;
goto _start;
}
else
{
lean_dec(v_fst_1639_);
lean_dec(v_lo_1633_);
return v_snd_1640_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___boxed(lean_object* v_n_1667_, lean_object* v_as_1668_, lean_object* v_lo_1669_, lean_object* v_hi_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v_n_1667_, v_as_1668_, v_lo_1669_, v_hi_1670_);
lean_dec(v_hi_1670_);
lean_dec(v_n_1667_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1(lean_object* v_stx_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1718_; lean_object* v___x_1726_; lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1768_; 
v___x_1726_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(v___y_1677_, v___y_1678_);
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1729_ = v___x_1726_;
v_isShared_1730_ = v_isSharedCheck_1768_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1768_;
goto v_resetjp_1728_;
}
v___jp_1680_:
{
size_t v_sz_1683_; size_t v___x_1684_; lean_object* v___x_1685_; 
v_sz_1683_ = lean_array_size(v___y_1682_);
v___x_1684_ = ((size_t)0ULL);
lean_inc_ref(v___y_1681_);
v___x_1685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(v___y_1682_, v_sz_1683_, v___x_1684_, v___y_1681_, v___y_1677_, v___y_1678_);
lean_dec_ref(v___y_1682_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1693_; 
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; 
v_unused_1694_ = lean_ctor_get(v___x_1685_, 0);
lean_dec(v_unused_1694_);
v___x_1687_ = v___x_1685_;
v_isShared_1688_ = v_isSharedCheck_1693_;
goto v_resetjp_1686_;
}
else
{
lean_dec(v___x_1685_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1693_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1689_ = lean_box(0);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1689_);
v___x_1691_ = v___x_1687_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
v_a_1695_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1685_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1685_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
v___jp_1703_:
{
lean_object* v___x_1709_; 
v___x_1709_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v___y_1704_, v___y_1705_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec(v___y_1704_);
v___y_1681_ = v___y_1706_;
v___y_1682_ = v___x_1709_;
goto v___jp_1680_;
}
v___jp_1710_:
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_nat_dec_le(v___y_1715_, v___y_1714_);
if (v___x_1716_ == 0)
{
lean_dec(v___y_1714_);
lean_inc(v___y_1715_);
v___y_1704_ = v___y_1711_;
v___y_1705_ = v___y_1712_;
v___y_1706_ = v___y_1713_;
v___y_1707_ = v___y_1715_;
v___y_1708_ = v___y_1715_;
goto v___jp_1703_;
}
else
{
v___y_1704_ = v___y_1711_;
v___y_1705_ = v___y_1712_;
v___y_1706_ = v___y_1713_;
v___y_1707_ = v___y_1715_;
v___y_1708_ = v___y_1714_;
goto v___jp_1703_;
}
}
v___jp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1719_ = lean_unsigned_to_nat(0u);
v___x_1720_ = ((lean_object*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0));
v___x_1721_ = lean_array_get_size(v___y_1718_);
v___x_1722_ = lean_nat_dec_eq(v___x_1721_, v___x_1719_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1723_ = lean_unsigned_to_nat(1u);
v___x_1724_ = lean_nat_sub(v___x_1721_, v___x_1723_);
v___x_1725_ = lean_nat_dec_le(v___x_1719_, v___x_1724_);
if (v___x_1725_ == 0)
{
lean_inc(v___x_1724_);
v___y_1711_ = v___x_1721_;
v___y_1712_ = v___y_1718_;
v___y_1713_ = v___x_1720_;
v___y_1714_ = v___x_1724_;
v___y_1715_ = v___x_1724_;
goto v___jp_1710_;
}
else
{
v___y_1711_ = v___x_1721_;
v___y_1712_ = v___y_1718_;
v___y_1713_ = v___x_1720_;
v___y_1714_ = v___x_1724_;
v___y_1715_ = v___x_1719_;
goto v___jp_1710_;
}
}
else
{
v___y_1681_ = v___x_1720_;
v___y_1682_ = v___y_1718_;
goto v___jp_1680_;
}
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; uint8_t v___y_1733_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1731_ = lean_st_ref_get(v___y_1678_);
v___x_1764_ = l_Lean_Linter_Clippy_linter_clippy_unnecessarySeqFocus;
v___x_1765_ = l_Lean_Linter_getLinterValueClippy(v___x_1764_, v_a_1727_);
lean_dec(v_a_1727_);
if (v___x_1765_ == 0)
{
lean_dec(v___x_1731_);
v___y_1733_ = v___x_1765_;
goto v___jp_1732_;
}
else
{
lean_object* v_infoState_1766_; uint8_t v_enabled_1767_; 
v_infoState_1766_ = lean_ctor_get(v___x_1731_, 8);
lean_inc_ref(v_infoState_1766_);
lean_dec(v___x_1731_);
v_enabled_1767_ = lean_ctor_get_uint8(v_infoState_1766_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1766_);
v___y_1733_ = v_enabled_1767_;
goto v___jp_1732_;
}
v___jp_1732_:
{
if (v___y_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
lean_dec(v_stx_1676_);
v___x_1734_ = lean_box(0);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v___x_1734_);
v___x_1736_ = v___x_1729_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
else
{
lean_object* v___x_1738_; lean_object* v_messages_1739_; uint8_t v___x_1740_; 
v___x_1738_ = lean_st_ref_get(v___y_1678_);
v_messages_1739_ = lean_ctor_get(v___x_1738_, 1);
lean_inc_ref(v_messages_1739_);
lean_dec(v___x_1738_);
v___x_1740_ = l_Lean_MessageLog_hasErrors(v_messages_1739_);
lean_dec_ref(v_messages_1739_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v_a_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___f_1745_; lean_object* v___x_1746_; lean_object* v_snd_1747_; lean_object* v_buckets_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
lean_del_object(v___x_1729_);
v___x_1741_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_1678_);
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref(v___x_1741_);
v___x_1743_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_multigoalKindsRef;
v___x_1744_ = lean_st_ref_get(v___x_1743_);
v___f_1745_ = lean_alloc_closure((void*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1745_, 0, v_stx_1676_);
lean_closure_set(v___f_1745_, 1, v___x_1744_);
lean_closure_set(v___f_1745_, 2, v_a_1742_);
v___x_1746_ = l_runST___redArg(v___f_1745_);
v_snd_1747_ = lean_ctor_get(v___x_1746_, 1);
lean_inc(v_snd_1747_);
lean_dec(v___x_1746_);
v_buckets_1748_ = lean_ctor_get(v_snd_1747_, 1);
lean_inc_ref(v_buckets_1748_);
lean_dec(v_snd_1747_);
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = ((lean_object*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1));
v___x_1751_ = lean_array_get_size(v_buckets_1748_);
v___x_1752_ = lean_nat_dec_lt(v___x_1749_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_dec_ref(v_buckets_1748_);
v___y_1718_ = v___x_1750_;
goto v___jp_1717_;
}
else
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_nat_dec_le(v___x_1751_, v___x_1751_);
if (v___x_1753_ == 0)
{
if (v___x_1752_ == 0)
{
lean_dec_ref(v_buckets_1748_);
v___y_1718_ = v___x_1750_;
goto v___jp_1717_;
}
else
{
size_t v___x_1754_; size_t v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = ((size_t)0ULL);
v___x_1755_ = lean_usize_of_nat(v___x_1751_);
v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(v___x_1740_, v_buckets_1748_, v___x_1754_, v___x_1755_, v___x_1750_);
lean_dec_ref(v_buckets_1748_);
v___y_1718_ = v___x_1756_;
goto v___jp_1717_;
}
}
else
{
size_t v___x_1757_; size_t v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = ((size_t)0ULL);
v___x_1758_ = lean_usize_of_nat(v___x_1751_);
v___x_1759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(v___x_1740_, v_buckets_1748_, v___x_1757_, v___x_1758_, v___x_1750_);
lean_dec_ref(v_buckets_1748_);
v___y_1718_ = v___x_1759_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1762_; 
lean_dec(v_stx_1676_);
v___x_1760_ = lean_box(0);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v___x_1760_);
v___x_1762_ = v___x_1729_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___boxed(lean_object* v_stx_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1(v_stx_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1(lean_object* v_o_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_o_1789_, v___y_1791_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___boxed(lean_object* v_o_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1(v_o_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5(lean_object* v_n_1799_, lean_object* v_as_1800_, lean_object* v_lo_1801_, lean_object* v_hi_1802_, lean_object* v_w_1803_, lean_object* v_hlo_1804_, lean_object* v_hhi_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v_n_1799_, v_as_1800_, v_lo_1801_, v_hi_1802_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___boxed(lean_object* v_n_1807_, lean_object* v_as_1808_, lean_object* v_lo_1809_, lean_object* v_hi_1810_, lean_object* v_w_1811_, lean_object* v_hlo_1812_, lean_object* v_hhi_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5(v_n_1807_, v_as_1808_, v_lo_1809_, v_hi_1810_, v_w_1811_, v_hlo_1812_, v_hhi_1813_);
lean_dec(v_hi_1810_);
lean_dec(v_n_1807_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7(lean_object* v_n_1815_, lean_object* v_lo_1816_, lean_object* v_hi_1817_, lean_object* v_hhi_1818_, lean_object* v_pivot_1819_, lean_object* v_as_1820_, lean_object* v_i_1821_, lean_object* v_k_1822_, lean_object* v_ilo_1823_, lean_object* v_ik_1824_, lean_object* v_w_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(v_hi_1817_, v_pivot_1819_, v_as_1820_, v_i_1821_, v_k_1822_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___boxed(lean_object* v_n_1827_, lean_object* v_lo_1828_, lean_object* v_hi_1829_, lean_object* v_hhi_1830_, lean_object* v_pivot_1831_, lean_object* v_as_1832_, lean_object* v_i_1833_, lean_object* v_k_1834_, lean_object* v_ilo_1835_, lean_object* v_ik_1836_, lean_object* v_w_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7(v_n_1827_, v_lo_1828_, v_hi_1829_, v_hhi_1830_, v_pivot_1831_, v_as_1832_, v_i_1833_, v_k_1834_, v_ilo_1835_, v_ik_1836_, v_w_1837_);
lean_dec(v_hi_1829_);
lean_dec(v_lo_1828_);
lean_dec(v_n_1827_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10(lean_object* v_msgData_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___redArg(v_msgData_1839_, v___y_1841_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___boxed(lean_object* v_msgData_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10(v_msgData_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = ((lean_object*)(l_Lean_Linter_Clippy_UnnecessarySeqFocus_unnecessarySeqFocusLinter));
v___x_1851_ = l_Lean_Elab_Command_addLinter(v___x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2____boxed(lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_();
return v_res_1853_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Clippy_UnnecessarySeqFocus(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_2107802180____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_Clippy_linter_clippy_unnecessarySeqFocus = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_Clippy_linter_clippy_unnecessarySeqFocus);
lean_dec_ref(res);
res = l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_Clippy_UnnecessarySeqFocus_multigoalKindsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_Clippy_UnnecessarySeqFocus_multigoalKindsRef);
lean_dec_ref(res);
res = l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_Clippy_UnnecessarySeqFocus_0__Lean_Linter_Clippy_initFn_00___x40_Lean_Linter_Clippy_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Clippy_UnnecessarySeqFocus(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Clippy_UnnecessarySeqFocus(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Clippy_UnnecessarySeqFocus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Clippy_UnnecessarySeqFocus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Clippy_UnnecessarySeqFocus(builtin);
}
#ifdef __cplusplus
}
#endif
