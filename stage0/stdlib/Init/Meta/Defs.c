// Lean compiler output
// Module: Init.Meta.Defs
// Imports: import all Init.Prelude public import Init.Data.Array.Basic public import Init.MetaTypes import Init.Data.Array.GetLit import Init.Data.Char.Basic meta import Init.MetaTypes import Init.WFTactics
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_any(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_substring_drop(lean_object*, lean_object*);
uint8_t lean_substring_all(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_string_contains(lean_object*, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t lean_string_isprefixof(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_string_isempty(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
lean_object* lean_string_nextwhile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instReprSourceInfo_repr(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_substring_tostring(lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*, uint8_t);
uint32_t lean_substring_front(lean_object*);
uint8_t lean_substring_isempty(lean_object*);
lean_object* lean_substring_takewhile(lean_object*, lean_object*);
lean_object* lean_substring_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_pos_min(lean_object*, lean_object*);
lean_object* lean_substring_prev(lean_object*, lean_object*);
uint32_t lean_substring_get(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(lean_object*);
uint32_t lean_string_front(lean_object*);
lean_object* lean_string_drop(lean_object*, lean_object*);
lean_object* lean_string_dropright(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_string_pos_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Lean_Macro_expandMacro_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* lean_nat_pred(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_substring_beq(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Char_quote(uint32_t);
lean_object* lean_string_trim(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getTrailing_x3f(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntaxArray_mkImpl___boxed(lean_object*, lean_object*);
lean_object* lean_string_capitalize(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* lean_version_get_major(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMajor___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_major___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_version_major___closed__0;
LEAN_EXPORT lean_object* l_Lean_version_major;
lean_object* lean_version_get_minor(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMinor___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_minor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_version_minor___closed__0;
LEAN_EXPORT lean_object* l_Lean_version_minor;
lean_object* lean_version_get_patch(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getPatch___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_patch___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_version_patch___closed__0;
LEAN_EXPORT lean_object* l_Lean_version_patch;
lean_object* lean_get_githash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getGithash___boxed(lean_object*);
static lean_once_cell_t l_Lean_githash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_githash___closed__0;
LEAN_EXPORT lean_object* l_Lean_githash;
uint8_t lean_version_get_is_release(lean_object*);
LEAN_EXPORT lean_object* l_Lean_version_getIsRelease___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_isRelease___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_version_isRelease___closed__0;
LEAN_EXPORT uint8_t l_Lean_version_isRelease;
lean_object* lean_version_get_special_desc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_version_getSpecialDesc___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_specialDesc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_version_specialDesc___closed__0;
LEAN_EXPORT lean_object* l_Lean_version_specialDesc;
static lean_once_cell_t l_Lean_versionStringCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__0;
static const lean_string_object l_Lean_versionStringCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_versionStringCore___closed__1 = (const lean_object*)&l_Lean_versionStringCore___closed__1_value;
static lean_once_cell_t l_Lean_versionStringCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__2;
static lean_once_cell_t l_Lean_versionStringCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__3;
static lean_once_cell_t l_Lean_versionStringCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__4;
static lean_once_cell_t l_Lean_versionStringCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__5;
static lean_once_cell_t l_Lean_versionStringCore___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__6;
static lean_once_cell_t l_Lean_versionStringCore___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__7;
LEAN_EXPORT lean_object* l_Lean_versionStringCore;
static const lean_string_object l_Lean_versionString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_versionString___closed__0 = (const lean_object*)&l_Lean_versionString___closed__0_value;
static lean_once_cell_t l_Lean_versionString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_versionString___closed__1;
static const lean_string_object l_Lean_versionString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_versionString___closed__2 = (const lean_object*)&l_Lean_versionString___closed__2_value;
static lean_once_cell_t l_Lean_versionString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionString___closed__3;
static lean_once_cell_t l_Lean_versionString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionString___closed__4;
static const lean_string_object l_Lean_versionString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", commit "};
static const lean_object* l_Lean_versionString___closed__5 = (const lean_object*)&l_Lean_versionString___closed__5_value;
static lean_once_cell_t l_Lean_versionString___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionString___closed__6;
static lean_once_cell_t l_Lean_versionString___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionString___closed__7;
LEAN_EXPORT lean_object* l_Lean_versionString;
static const lean_string_object l_Lean_origin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "leanprover/lean4"};
static const lean_object* l_Lean_origin___closed__0 = (const lean_object*)&l_Lean_origin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_origin = (const lean_object*)&l_Lean_origin___closed__0_value;
static const lean_string_object l_Lean_toolchain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_toolchain___closed__0 = (const lean_object*)&l_Lean_toolchain___closed__0_value;
static lean_once_cell_t l_Lean_toolchain___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__1;
static lean_once_cell_t l_Lean_toolchain___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__2;
static lean_once_cell_t l_Lean_toolchain___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__3;
static lean_once_cell_t l_Lean_toolchain___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__4;
static lean_once_cell_t l_Lean_toolchain___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__5;
LEAN_EXPORT lean_object* l_Lean_toolchain;
uint8_t lean_internal_is_stage0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Internal_isStage0___boxed(lean_object*);
uint8_t lean_internal_has_llvm_backend(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Internal_hasLLVMBackend___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isGreek(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isGreek___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isLetterLike(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isLetterLike___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isNumericSubscript(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isNumericSubscript___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isSubScriptAlnum(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIdFirst(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isIdFirst___boxed(lean_object*);
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object*);
static lean_once_cell_t l_Lean_isIdFirstAscii___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_isIdFirstAscii___closed__0;
LEAN_EXPORT uint8_t l_Lean_isIdFirstAscii(uint8_t);
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object*);
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1;
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIdRest(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object*);
static lean_once_cell_t l_Lean_isIdRestAscii___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_isIdRestAscii___closed__0;
static lean_once_cell_t l_Lean_isIdRestAscii___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_isIdRestAscii___closed__1;
static lean_once_cell_t l_Lean_isIdRestAscii___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_isIdRestAscii___closed__2;
LEAN_EXPORT uint8_t l_Lean_isIdRestAscii(uint8_t);
LEAN_EXPORT lean_object* l_Lean_isIdRestAscii___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_idBeginEscape;
LEAN_EXPORT uint32_t l_Lean_idEndEscape;
LEAN_EXPORT uint8_t l_Lean_isIdBeginEscape(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isIdBeginEscape___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIdEndEscape(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isIdEndEscape___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getRoot___boxed(lean_object*);
static const lean_string_object l_Lean_Name_isInaccessibleUserName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "_inaccessible"};
static const lean_object* l_Lean_Name_isInaccessibleUserName___closed__0 = (const lean_object*)&l_Lean_Name_isInaccessibleUserName___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Name_isInaccessibleUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isInaccessibleUserName___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_isIdRest___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___boxed(lean_object*);
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_isIdEndEscape___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object*);
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0_value;
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed(lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0_value;
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3_value;
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_hasNum(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_hasNum___boxed(lean_object*);
static const lean_string_object l_Lean_Name_reprPrec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Name.anonymous"};
static const lean_object* l_Lean_Name_reprPrec___closed__0 = (const lean_object*)&l_Lean_Name_reprPrec___closed__0_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__0_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__1 = (const lean_object*)&l_Lean_Name_reprPrec___closed__1_value;
static const lean_string_object l_Lean_Name_reprPrec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Name_reprPrec___closed__2 = (const lean_object*)&l_Lean_Name_reprPrec___closed__2_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__2_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__3 = (const lean_object*)&l_Lean_Name_reprPrec___closed__3_value;
static const lean_string_object l_Lean_Name_reprPrec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Name.mkStr "};
static const lean_object* l_Lean_Name_reprPrec___closed__4 = (const lean_object*)&l_Lean_Name_reprPrec___closed__4_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__4_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__5 = (const lean_object*)&l_Lean_Name_reprPrec___closed__5_value;
static const lean_string_object l_Lean_Name_reprPrec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Name_reprPrec___closed__6 = (const lean_object*)&l_Lean_Name_reprPrec___closed__6_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__6_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__7 = (const lean_object*)&l_Lean_Name_reprPrec___closed__7_value;
static const lean_string_object l_Lean_Name_reprPrec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Name.mkNum "};
static const lean_object* l_Lean_Name_reprPrec___closed__8 = (const lean_object*)&l_Lean_Name_reprPrec___closed__8_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__8_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__9 = (const lean_object*)&l_Lean_Name_reprPrec___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Name_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_reprPrec___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Name_instRepr___closed__0 = (const lean_object*)&l_Lean_Name_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Name_instRepr = (const lean_object*)&l_Lean_Name_instRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_name_append_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_name_append_before(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_instDecidableEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2_value;
static const lean_string_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5_value;
static const lean_string_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7;
static lean_once_cell_t l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Lean_Syntax_instReprPreresolved_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Syntax.Preresolved.namespace"};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__0 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instReprPreresolved_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__1 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_instReprPreresolved_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__2 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__2_value;
static lean_once_cell_t l_Lean_Syntax_instReprPreresolved_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__3;
static lean_once_cell_t l_Lean_Syntax_instReprPreresolved_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__4;
static const lean_string_object l_Lean_Syntax_instReprPreresolved_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Syntax.Preresolved.decl"};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__5 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__5_value;
static const lean_ctor_object l_Lean_Syntax_instReprPreresolved_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__5_value)}};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__6 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__6_value;
static const lean_ctor_object l_Lean_Syntax_instReprPreresolved_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__7 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instReprPreresolved___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instReprPreresolved_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instReprPreresolved___closed__0 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instReprPreresolved = (const lean_object*)&l_Lean_Syntax_instReprPreresolved___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object*);
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Syntax.missing"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__0 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__1 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__1_value;
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Syntax.node"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__2 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__2_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__2_value)}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__3 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__3_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__4 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__4_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1;
static lean_once_cell_t l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2;
static const lean_ctor_object l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Syntax.atom"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__5 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__5_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__5_value)}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__6 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__6_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__7 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__7_value;
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Syntax.ident"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__8 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__8_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__8_value)}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__9 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__9_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__10 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__10_value;
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ".toRawSubstring"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__11 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instRepr_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instRepr___closed__0 = (const lean_object*)&l_Lean_Syntax_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instRepr = (const lean_object*)&l_Lean_Syntax_instRepr___closed__0_value;
static const lean_string_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "raw"};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7;
static const lean_string_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9;
static lean_once_cell_t l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0 = (const lean_object*)&l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_TSyntax_instCoeIdentTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TSyntax_instCoeIdentTerm___closed__0 = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeIdentTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeStrLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeNameLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeScientificLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeNumLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeCharLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeIdentLevel = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeNumLitPrio = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeNumLitPrec = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instBEqPreresolved___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instBEqPreresolved_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instBEqPreresolved___closed__0 = (const lean_object*)&l_Lean_Syntax_instBEqPreresolved___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instBEqPreresolved = (const lean_object*)&l_Lean_Syntax_instBEqPreresolved___closed__0_value;
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_structEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instBEq___closed__0 = (const lean_object*)&l_Lean_Syntax_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instBEq = (const lean_object*)&l_Lean_Syntax_instBEq___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_expandMacros___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_expandMacros___lam__0___closed__0 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value;
static const lean_string_object l_Lean_expandMacros___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_expandMacros___lam__0___closed__1 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value;
static const lean_string_object l_Lean_expandMacros___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_expandMacros___lam__0___closed__2 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value;
static const lean_string_object l_Lean_expandMacros___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lean_expandMacros___lam__0___closed__3 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_expandMacros___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_expandMacros___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_expandMacros___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_expandMacros___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_expandMacros___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_expandMacros___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_expandMacros___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_expandMacros___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Lean_expandMacros___lam__0___closed__4 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__4_value;
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_expandMacros___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___closed__0_value;
static const lean_string_object l_Lean_expandMacros___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_expandMacros___closed__0 = (const lean_object*)&l_Lean_expandMacros___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCIdentFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_internal"};
static const lean_object* l_Lean_mkCIdentFrom___closed__0 = (const lean_object*)&l_Lean_mkCIdentFrom___closed__0_value;
static const lean_ctor_object l_Lean_mkCIdentFrom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCIdentFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 131, 204, 40, 20, 233, 244, 88)}};
static const lean_object* l_Lean_mkCIdentFrom___closed__1 = (const lean_object*)&l_Lean_mkCIdentFrom___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdent(lean_object*);
static const lean_string_object l_Lean_mkGroupNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_mkGroupNode___closed__0 = (const lean_object*)&l_Lean_mkGroupNode___closed__0_value;
static const lean_ctor_object l_Lean_mkGroupNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkGroupNode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_mkGroupNode___closed__1 = (const lean_object*)&l_Lean_mkGroupNode___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_mkSepArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_mkSepArray___closed__0 = (const lean_object*)&l_Lean_mkSepArray___closed__0_value;
static const lean_ctor_object l_Lean_mkSepArray___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkSepArray___closed__0_value)}};
static const lean_object* l_Lean_mkSepArray___closed__1 = (const lean_object*)&l_Lean_mkSepArray___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkOptionalNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_mkOptionalNode___closed__0 = (const lean_object*)&l_Lean_mkOptionalNode___closed__0_value;
static const lean_ctor_object l_Lean_mkOptionalNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkOptionalNode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_mkOptionalNode___closed__1 = (const lean_object*)&l_Lean_mkOptionalNode___closed__1_value;
static const lean_ctor_object l_Lean_mkOptionalNode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_mkOptionalNode___closed__1_value),((lean_object*)&l_Lean_mkSepArray___closed__0_value)}};
static const lean_object* l_Lean_mkOptionalNode___closed__2 = (const lean_object*)&l_Lean_mkOptionalNode___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object*);
static const lean_string_object l_Lean_mkHole___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_mkHole___closed__0 = (const lean_object*)&l_Lean_mkHole___closed__0_value;
static const lean_ctor_object l_Lean_mkHole___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_mkHole___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkHole___closed__1_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_mkHole___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkHole___closed__1_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_mkHole___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkHole___closed__1_value_aux_2),((lean_object*)&l_Lean_mkHole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_mkHole___closed__1 = (const lean_object*)&l_Lean_mkHole___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Syntax_SepArray_ofElems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_SepArray_ofElems___closed__0 = (const lean_object*)&l_Lean_Syntax_SepArray_ofElems___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_SepArray_ofElems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_mkOptionalNode___closed__1_value),((lean_object*)&l_Lean_Syntax_SepArray_ofElems___closed__0_value)}};
static const lean_object* l_Lean_Syntax_SepArray_ofElems___closed__1 = (const lean_object*)&l_Lean_Syntax_SepArray_ofElems___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeArraySepArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Syntax_mkApp___closed__0 = (const lean_object*)&l_Lean_Syntax_mkApp___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkApp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_mkApp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkApp___closed__1_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Syntax_mkApp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkApp___closed__1_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Syntax_mkApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkApp___closed__1_value_aux_2),((lean_object*)&l_Lean_Syntax_mkApp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Syntax_mkApp___closed__1 = (const lean_object*)&l_Lean_Syntax_mkApp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkCharLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l_Lean_Syntax_mkCharLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkCharLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkCharLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkCharLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l_Lean_Syntax_mkCharLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkCharLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkStrLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Syntax_mkStrLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkStrLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkStrLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkStrLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Syntax_mkStrLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkStrLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkNumLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Syntax_mkNumLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkNumLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkNumLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkNumLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Syntax_mkNumLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkNumLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkScientificLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l_Lean_Syntax_mkScientificLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkScientificLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkScientificLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkScientificLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l_Lean_Syntax_mkScientificLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkScientificLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkNameLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Syntax_mkNameLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkNameLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkNameLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkNameLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_Syntax_mkNameLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkNameLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Syntax_decodeNatLitVal_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_decodeNatLitVal_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Syntax_isFieldIdx_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fieldIdx"};
static const lean_object* l_Lean_Syntax_isFieldIdx_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_isFieldIdx_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_isFieldIdx_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_isFieldIdx_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 141, 165, 29, 238, 211, 61, 163)}};
static const lean_object* l_Lean_Syntax_isFieldIdx_x3f___closed__1 = (const lean_object*)&l_Lean_Syntax_isFieldIdx_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_decodeStringGap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_decodeStringGap___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_decodeStringGap___closed__0 = (const lean_object*)&l_Lean_Syntax_decodeStringGap___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object*);
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0_value;
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_value;
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__2 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object*);
static const lean_string_object l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Init.Meta.Defs"};
static const lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0 = (const lean_object*)&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0_value;
static const lean_string_object l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Substring.Raw.toName"};
static const lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1 = (const lean_object*)&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1_value;
static const lean_string_object l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2 = (const lean_object*)&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2_value;
static lean_once_cell_t l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3;
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object*);
LEAN_EXPORT lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object*);
static const lean_ctor_object l_Lean_TSyntax_getScientific___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_TSyntax_getScientific___closed__0 = (const lean_object*)&l_Lean_TSyntax_getScientific___closed__0_value;
static const lean_ctor_object l_Lean_TSyntax_getScientific___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_TSyntax_getScientific___closed__0_value)}};
static const lean_object* l_Lean_TSyntax_getScientific___closed__1 = (const lean_object*)&l_Lean_TSyntax_getScientific___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instQuoteTermMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_instQuoteTermMkStr1___closed__0 = (const lean_object*)&l_Lean_instQuoteTermMkStr1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteTermMkStr1 = (const lean_object*)&l_Lean_instQuoteTermMkStr1___closed__0_value;
static const lean_string_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__0 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__0_value;
static const lean_string_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__1 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__2 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__3;
static const lean_string_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__4 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__5 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instQuoteBoolMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteBoolMkStr1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteBoolMkStr1___closed__0 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteBoolMkStr1 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instQuoteCharCharLitKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteCharCharLitKind___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteCharCharLitKind___closed__0 = (const lean_object*)&l_Lean_instQuoteCharCharLitKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteCharCharLitKind = (const lean_object*)&l_Lean_instQuoteCharCharLitKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object*);
static const lean_closure_object l_Lean_instQuoteStringStrLitKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteStringStrLitKind___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteStringStrLitKind___closed__0 = (const lean_object*)&l_Lean_instQuoteStringStrLitKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteStringStrLitKind = (const lean_object*)&l_Lean_instQuoteStringStrLitKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object*);
static const lean_closure_object l_Lean_instQuoteNatNumLitKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteNatNumLitKind___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteNatNumLitKind___closed__0 = (const lean_object*)&l_Lean_instQuoteNatNumLitKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteNatNumLitKind = (const lean_object*)&l_Lean_instQuoteNatNumLitKind___closed__0_value;
static const lean_string_object l_Lean_instQuoteRawMkStr1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_instQuoteRawMkStr1___lam__0___closed__0 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__0_value;
static const lean_string_object l_Lean_instQuoteRawMkStr1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "toRawSubstring'"};
static const lean_object* l_Lean_instQuoteRawMkStr1___lam__0___closed__1 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instQuoteRawMkStr1___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_Lean_instQuoteRawMkStr1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(190, 31, 121, 163, 121, 213, 247, 150)}};
static const lean_object* l_Lean_instQuoteRawMkStr1___lam__0___closed__2 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object*);
static const lean_closure_object l_Lean_instQuoteRawMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteRawMkStr1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteRawMkStr1___closed__0 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteRawMkStr1 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___closed__0_value;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
static const lean_string_object l_Lean_quoteNameMk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l_Lean_quoteNameMk___closed__0 = (const lean_object*)&l_Lean_quoteNameMk___closed__0_value;
static const lean_string_object l_Lean_quoteNameMk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "anonymous"};
static const lean_object* l_Lean_quoteNameMk___closed__1 = (const lean_object*)&l_Lean_quoteNameMk___closed__1_value;
static const lean_ctor_object l_Lean_quoteNameMk___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__2_value_aux_0),((lean_object*)&l_Lean_quoteNameMk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__2_value_aux_1),((lean_object*)&l_Lean_quoteNameMk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(155, 163, 3, 148, 15, 163, 84, 121)}};
static const lean_object* l_Lean_quoteNameMk___closed__2 = (const lean_object*)&l_Lean_quoteNameMk___closed__2_value;
static lean_once_cell_t l_Lean_quoteNameMk___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_quoteNameMk___closed__3;
static const lean_string_object l_Lean_quoteNameMk___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mkStr"};
static const lean_object* l_Lean_quoteNameMk___closed__4 = (const lean_object*)&l_Lean_quoteNameMk___closed__4_value;
static const lean_ctor_object l_Lean_quoteNameMk___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__5_value_aux_0),((lean_object*)&l_Lean_quoteNameMk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__5_value_aux_1),((lean_object*)&l_Lean_quoteNameMk___closed__4_value),LEAN_SCALAR_PTR_LITERAL(66, 239, 13, 154, 0, 241, 98, 75)}};
static const lean_object* l_Lean_quoteNameMk___closed__5 = (const lean_object*)&l_Lean_quoteNameMk___closed__5_value;
static const lean_string_object l_Lean_quoteNameMk___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mkNum"};
static const lean_object* l_Lean_quoteNameMk___closed__6 = (const lean_object*)&l_Lean_quoteNameMk___closed__6_value;
static const lean_ctor_object l_Lean_quoteNameMk___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__7_value_aux_0),((lean_object*)&l_Lean_quoteNameMk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__7_value_aux_1),((lean_object*)&l_Lean_quoteNameMk___closed__6_value),LEAN_SCALAR_PTR_LITERAL(247, 141, 7, 17, 149, 107, 178, 15)}};
static const lean_object* l_Lean_quoteNameMk___closed__7 = (const lean_object*)&l_Lean_quoteNameMk___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object*);
static const lean_string_object l_Lean_instQuoteNameMkStr1___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean_instQuoteNameMkStr1___private__1___closed__0 = (const lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__0_value;
static const lean_ctor_object l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_instQuoteNameMkStr1___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_2),((lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lean_instQuoteNameMkStr1___private__1___closed__1 = (const lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object*);
static const lean_closure_object l_Lean_instQuoteNameMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteNameMkStr1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteNameMkStr1___closed__0 = (const lean_object*)&l_Lean_instQuoteNameMkStr1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteNameMkStr1 = (const lean_object*)&l_Lean_instQuoteNameMkStr1___closed__0_value;
static const lean_string_object l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mkArray"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Option_hasQuote___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Option_hasQuote___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Option_hasQuote___redArg___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Option_hasQuote___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__3;
static const lean_string_object l_Lean_Option_hasQuote___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Option_hasQuote___redArg___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Option_hasQuote___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_evalPrec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_evalPrec___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_evalPrec___closed__0 = (const lean_object*)&l_Lean_evalPrec___closed__0_value;
static const lean_string_object l_Lean_evalPrec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected precedence"};
static const lean_object* l_Lean_evalPrec___closed__1 = (const lean_object*)&l_Lean_evalPrec___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_evalPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unexpected priority"};
static const lean_object* l_Lean_evalPrio___closed__0 = (const lean_object*)&l_Lean_evalPrio___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_getSepElems___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_getSepElems___redArg___closed__0 = (const lean_object*)&l_Array_getSepElems___redArg___closed__0_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__1 = (const lean_object*)&l_Array_getSepElems___redArg___closed__1_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__2 = (const lean_object*)&l_Array_getSepElems___redArg___closed__2_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__3 = (const lean_object*)&l_Array_getSepElems___redArg___closed__3_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__4 = (const lean_object*)&l_Array_getSepElems___redArg___closed__4_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__5 = (const lean_object*)&l_Array_getSepElems___redArg___closed__5_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__6 = (const lean_object*)&l_Array_getSepElems___redArg___closed__6_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__7 = (const lean_object*)&l_Array_getSepElems___redArg___closed__7_value;
static const lean_ctor_object l_Array_getSepElems___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_getSepElems___redArg___closed__1_value),((lean_object*)&l_Array_getSepElems___redArg___closed__2_value)}};
static const lean_object* l_Array_getSepElems___redArg___closed__8 = (const lean_object*)&l_Array_getSepElems___redArg___closed__8_value;
static const lean_ctor_object l_Array_getSepElems___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_getSepElems___redArg___closed__8_value),((lean_object*)&l_Array_getSepElems___redArg___closed__3_value),((lean_object*)&l_Array_getSepElems___redArg___closed__4_value),((lean_object*)&l_Array_getSepElems___redArg___closed__5_value),((lean_object*)&l_Array_getSepElems___redArg___closed__6_value)}};
static const lean_object* l_Array_getSepElems___redArg___closed__9 = (const lean_object*)&l_Array_getSepElems___redArg___closed__9_value;
static const lean_ctor_object l_Array_getSepElems___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_getSepElems___redArg___closed__9_value),((lean_object*)&l_Array_getSepElems___redArg___closed__7_value)}};
static const lean_object* l_Array_getSepElems___redArg___closed__10 = (const lean_object*)&l_Array_getSepElems___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutSepArrayArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object*);
static const lean_string_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value;
static const lean_string_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instCoeTermTSyntaxConsSyntaxNodeKindMkStr4Nil = (const lean_object*)&l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object*);
static const lean_string_object l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "interpolatedStrLitKind"};
static const lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 181, 130, 246, 88, 58, 26, 43)}};
static const lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1 = (const lean_object*)&l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_++_"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 69, 86, 178, 149, 48, 216, 23)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "++"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_TSyntax_expandInterpolatedStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__0 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__0_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__1 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__1_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_2),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__2 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__2_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__3 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__3_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_2),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__4 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__4_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__5 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__5_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__6 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__6_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__7 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__7_value;
static lean_once_cell_t l_Lean_TSyntax_expandInterpolatedStr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__8;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "TSyntax"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__9 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__9_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__10_value_aux_0),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(208, 86, 51, 178, 37, 75, 0, 6)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__10 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__10_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__10_value)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__11 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__11_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Compat"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__12 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__12_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__13_value_aux_0),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(208, 86, 51, 178, 37, 75, 0, 6)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__13_value_aux_1),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__12_value),LEAN_SCALAR_PTR_LITERAL(233, 134, 124, 217, 96, 118, 79, 86)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__13 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__13_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__13_value)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__14 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__14_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__15 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__15_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__11_value),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__15_value)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__16 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__16_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__17 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.TransparencyMode.all"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__0 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__1 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.TransparencyMode.default"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__2 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__3 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.TransparencyMode.reducible"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__4 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__5 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__5_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.TransparencyMode.instances"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__6 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__6_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__7 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__7_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.TransparencyMode.none"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__8 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__8_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__9 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__9_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.TransparencyMode.implicit"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__10 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__10_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__10_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__11 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprTransparencyMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprTransparencyMode_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprTransparencyMode___closed__0 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprTransparencyMode = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode___closed__0_value;
static const lean_string_object l_Lean_Meta_instReprEtaStructMode_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.EtaStructMode.all"};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__0 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprEtaStructMode_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__1 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_instReprEtaStructMode_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.EtaStructMode.notClasses"};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__2 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprEtaStructMode_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__3 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprEtaStructMode_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.EtaStructMode.none"};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__4 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprEtaStructMode_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__5 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprEtaStructMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprEtaStructMode_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprEtaStructMode___closed__0 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprEtaStructMode = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode___closed__0_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zeta"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__4;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "beta"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__6_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eta"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "etaStruct"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__9_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__11;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iota"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__13_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__15_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__18;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "autoUnfold"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__19_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__19_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__20_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__21;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "failIfUnchanged"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__22 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__22_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__22_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__23 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__23_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__24;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unfoldPartialApp"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__25 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__25_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__25_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__26 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__26_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__27;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "zetaDelta"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__28 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__28_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__28_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__29 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__29_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "index"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__30 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__30_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__30_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__31 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__31_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__32;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "zetaUnused"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__33 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__33_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__33_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__34 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__34_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "zetaHave"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__35 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__35_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__35_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__36 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__36_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__37;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "locals"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__38 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__38_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__38_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__39 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__39_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instances"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__40 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__40_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__40_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__41 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__41_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprConfig_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprConfig___closed__0 = (const lean_object*)&l_Lean_Meta_instReprConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprConfig = (const lean_object*)&l_Lean_Meta_instReprConfig___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__1_value)}};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0_value;
static const lean_string_object l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__1_value)}};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "maxSteps"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "maxDischargeDepth"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "contextual"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "memoize"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "singlePass"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arith"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ground"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "implicitDefEqProofs"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "catchRuntime"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letToHave"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "congrConsts"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bitVecOfNat"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "warnExponents"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "suggestions"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "maxSuggestions"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__38 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__38_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__38_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprConfig__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprConfig__1_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprConfig__1___closed__0 = (const lean_object*)&l_Lean_Meta_instReprConfig__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprConfig__1 = (const lean_object*)&l_Lean_Meta_instReprConfig__1___closed__0_value;
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_getConfigItems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_getConfigItems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__1_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_getConfigItems___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 254, 59, 95, 54, 234, 162, 220)}};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMajor___boxed(lean_object* v_u_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lean_version_get_major(v_u_2_);
return v_res_3_;
}
}
static lean_object* _init_l_Lean_version_major___closed__0(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_box(0);
v___x_5_ = lean_version_get_major(v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_version_major(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_obj_once(&l_Lean_version_major___closed__0, &l_Lean_version_major___closed__0_once, _init_l_Lean_version_major___closed__0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMinor___boxed(lean_object* v_u_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lean_version_get_minor(v_u_8_);
return v_res_9_;
}
}
static lean_object* _init_l_Lean_version_minor___closed__0(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_box(0);
v___x_11_ = lean_version_get_minor(v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_version_minor(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_version_minor___closed__0, &l_Lean_version_minor___closed__0_once, _init_l_Lean_version_minor___closed__0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getPatch___boxed(lean_object* v_u_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lean_version_get_patch(v_u_14_);
return v_res_15_;
}
}
static lean_object* _init_l_Lean_version_patch___closed__0(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_box(0);
v___x_17_ = lean_version_get_patch(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_version_patch(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_obj_once(&l_Lean_version_patch___closed__0, &l_Lean_version_patch___closed__0_once, _init_l_Lean_version_patch___closed__0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_getGithash___boxed(lean_object* v_u_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lean_get_githash(v_u_20_);
return v_res_21_;
}
}
static lean_object* _init_l_Lean_githash___closed__0(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_box(0);
v___x_23_ = lean_get_githash(v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_githash(void){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_obj_once(&l_Lean_githash___closed__0, &l_Lean_githash___closed__0_once, _init_l_Lean_githash___closed__0);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_version_getIsRelease___boxed(lean_object* v_u_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = lean_version_get_is_release(v_u_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
static uint8_t _init_l_Lean_version_isRelease___closed__0(void){
_start:
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = lean_box(0);
v___x_30_ = lean_version_get_is_release(v___x_29_);
return v___x_30_;
}
}
static uint8_t _init_l_Lean_version_isRelease(void){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_uint8_once(&l_Lean_version_isRelease___closed__0, &l_Lean_version_isRelease___closed__0_once, _init_l_Lean_version_isRelease___closed__0);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_version_getSpecialDesc___boxed(lean_object* v_u_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lean_version_get_special_desc(v_u_33_);
return v_res_34_;
}
}
static lean_object* _init_l_Lean_version_specialDesc___closed__0(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_box(0);
v___x_36_ = lean_version_get_special_desc(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_version_specialDesc(void){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_obj_once(&l_Lean_version_specialDesc___closed__0, &l_Lean_version_specialDesc___closed__0_once, _init_l_Lean_version_specialDesc___closed__0);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__0(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = l_Lean_version_major;
v___x_39_ = l_Nat_reprFast(v___x_38_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__2(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_42_ = lean_obj_once(&l_Lean_versionStringCore___closed__0, &l_Lean_versionStringCore___closed__0_once, _init_l_Lean_versionStringCore___closed__0);
v___x_43_ = lean_string_append(v___x_42_, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__3(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = l_Lean_version_minor;
v___x_45_ = l_Nat_reprFast(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__4(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&l_Lean_versionStringCore___closed__3, &l_Lean_versionStringCore___closed__3_once, _init_l_Lean_versionStringCore___closed__3);
v___x_47_ = lean_obj_once(&l_Lean_versionStringCore___closed__2, &l_Lean_versionStringCore___closed__2_once, _init_l_Lean_versionStringCore___closed__2);
v___x_48_ = lean_string_append(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__5(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_50_ = lean_obj_once(&l_Lean_versionStringCore___closed__4, &l_Lean_versionStringCore___closed__4_once, _init_l_Lean_versionStringCore___closed__4);
v___x_51_ = lean_string_append(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__6(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = l_Lean_version_patch;
v___x_53_ = l_Nat_reprFast(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__7(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Lean_versionStringCore___closed__6, &l_Lean_versionStringCore___closed__6_once, _init_l_Lean_versionStringCore___closed__6);
v___x_55_ = lean_obj_once(&l_Lean_versionStringCore___closed__5, &l_Lean_versionStringCore___closed__5_once, _init_l_Lean_versionStringCore___closed__5);
v___x_56_ = lean_string_append(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_versionStringCore(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_obj_once(&l_Lean_versionStringCore___closed__7, &l_Lean_versionStringCore___closed__7_once, _init_l_Lean_versionStringCore___closed__7);
return v___x_57_;
}
}
static uint8_t _init_l_Lean_versionString___closed__1(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_59_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_60_ = l_Lean_version_specialDesc;
v___x_61_ = lean_string_dec_eq(v___x_60_, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_versionString___closed__3(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = ((lean_object*)(l_Lean_versionString___closed__2));
v___x_64_ = l_Lean_versionStringCore;
v___x_65_ = lean_string_append(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_versionString___closed__4(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = l_Lean_version_specialDesc;
v___x_67_ = lean_obj_once(&l_Lean_versionString___closed__3, &l_Lean_versionString___closed__3_once, _init_l_Lean_versionString___closed__3);
v___x_68_ = lean_string_append(v___x_67_, v___x_66_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_versionString___closed__6(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = ((lean_object*)(l_Lean_versionString___closed__5));
v___x_71_ = l_Lean_versionStringCore;
v___x_72_ = lean_string_append(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_versionString___closed__7(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = l_Lean_githash;
v___x_74_ = lean_obj_once(&l_Lean_versionString___closed__6, &l_Lean_versionString___closed__6_once, _init_l_Lean_versionString___closed__6);
v___x_75_ = lean_string_append(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_versionString(void){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = lean_uint8_once(&l_Lean_versionString___closed__1, &l_Lean_versionString___closed__1_once, _init_l_Lean_versionString___closed__1);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_versionString___closed__4, &l_Lean_versionString___closed__4_once, _init_l_Lean_versionString___closed__4);
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = l_Lean_version_isRelease;
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Lean_versionString___closed__7, &l_Lean_versionString___closed__7_once, _init_l_Lean_versionString___closed__7);
return v___x_79_;
}
else
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_versionStringCore;
return v___x_80_;
}
}
}
}
static lean_object* _init_l_Lean_toolchain___closed__1(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_85_ = ((lean_object*)(l_Lean_origin___closed__0));
v___x_86_ = lean_string_append(v___x_85_, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__2(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = l_Lean_version_specialDesc;
v___x_88_ = lean_obj_once(&l_Lean_toolchain___closed__1, &l_Lean_toolchain___closed__1_once, _init_l_Lean_toolchain___closed__1);
v___x_89_ = lean_string_append(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__3(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = l_Lean_versionStringCore;
v___x_91_ = lean_obj_once(&l_Lean_toolchain___closed__1, &l_Lean_toolchain___closed__1_once, _init_l_Lean_toolchain___closed__1);
v___x_92_ = lean_string_append(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__4(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = ((lean_object*)(l_Lean_versionString___closed__2));
v___x_94_ = lean_obj_once(&l_Lean_toolchain___closed__3, &l_Lean_toolchain___closed__3_once, _init_l_Lean_toolchain___closed__3);
v___x_95_ = lean_string_append(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__5(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = l_Lean_version_specialDesc;
v___x_97_ = lean_obj_once(&l_Lean_toolchain___closed__4, &l_Lean_toolchain___closed__4_once, _init_l_Lean_toolchain___closed__4);
v___x_98_ = lean_string_append(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_toolchain(void){
_start:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_100_ = lean_uint8_once(&l_Lean_versionString___closed__1, &l_Lean_versionString___closed__1_once, _init_l_Lean_versionString___closed__1);
if (v___x_100_ == 0)
{
uint8_t v___x_101_; 
v___x_101_ = l_Lean_version_isRelease;
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_toolchain___closed__2, &l_Lean_toolchain___closed__2_once, _init_l_Lean_toolchain___closed__2);
return v___x_102_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lean_toolchain___closed__5, &l_Lean_toolchain___closed__5_once, _init_l_Lean_toolchain___closed__5);
return v___x_103_;
}
}
else
{
uint8_t v___x_104_; 
v___x_104_ = l_Lean_version_isRelease;
if (v___x_104_ == 0)
{
return v___x_99_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_toolchain___closed__3, &l_Lean_toolchain___closed__3_once, _init_l_Lean_toolchain___closed__3);
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_isStage0___boxed(lean_object* v_u_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = lean_internal_is_stage0(v_u_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_hasLLVMBackend___boxed(lean_object* v_u_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = lean_internal_has_llvm_backend(v_u_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT uint8_t l_Lean_isGreek(uint32_t v_c_114_){
_start:
{
uint32_t v___x_115_; uint8_t v___x_116_; 
v___x_115_ = 913;
v___x_116_ = lean_uint32_dec_le(v___x_115_, v_c_114_);
if (v___x_116_ == 0)
{
return v___x_116_;
}
else
{
uint32_t v___x_117_; uint8_t v___x_118_; 
v___x_117_ = 989;
v___x_118_ = lean_uint32_dec_le(v_c_114_, v___x_117_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isGreek___boxed(lean_object* v_c_119_){
_start:
{
uint32_t v_c_boxed_120_; uint8_t v_res_121_; lean_object* v_r_122_; 
v_c_boxed_120_ = lean_unbox_uint32(v_c_119_);
lean_dec(v_c_119_);
v_res_121_ = l_Lean_isGreek(v_c_boxed_120_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT uint8_t l_Lean_isLetterLike(uint32_t v_c_123_){
_start:
{
uint8_t v___y_130_; uint8_t v___y_136_; uint8_t v___y_142_; uint8_t v___y_148_; uint8_t v___y_154_; uint8_t v___y_165_; uint8_t v___y_176_; uint32_t v___x_179_; uint8_t v___x_180_; 
v___x_179_ = 945;
v___x_180_ = lean_uint32_dec_le(v___x_179_, v_c_123_);
if (v___x_180_ == 0)
{
v___y_176_ = v___x_180_;
goto v___jp_175_;
}
else
{
uint32_t v___x_181_; uint8_t v___x_182_; 
v___x_181_ = 969;
v___x_182_ = lean_uint32_dec_le(v_c_123_, v___x_181_);
v___y_176_ = v___x_182_;
goto v___jp_175_;
}
v___jp_124_:
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 256;
v___x_126_ = lean_uint32_dec_le(v___x_125_, v_c_123_);
if (v___x_126_ == 0)
{
return v___x_126_;
}
else
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 383;
v___x_128_ = lean_uint32_dec_le(v_c_123_, v___x_127_);
return v___x_128_;
}
}
v___jp_129_:
{
if (v___y_130_ == 0)
{
goto v___jp_124_;
}
else
{
uint32_t v___x_131_; uint8_t v___x_132_; 
v___x_131_ = 215;
v___x_132_ = lean_uint32_dec_eq(v_c_123_, v___x_131_);
if (v___x_132_ == 0)
{
uint32_t v___x_133_; uint8_t v___x_134_; 
v___x_133_ = 247;
v___x_134_ = lean_uint32_dec_eq(v_c_123_, v___x_133_);
if (v___x_134_ == 0)
{
return v___y_130_;
}
else
{
goto v___jp_124_;
}
}
else
{
goto v___jp_124_;
}
}
}
v___jp_135_:
{
if (v___y_136_ == 0)
{
uint32_t v___x_137_; uint8_t v___x_138_; 
v___x_137_ = 192;
v___x_138_ = lean_uint32_dec_le(v___x_137_, v_c_123_);
if (v___x_138_ == 0)
{
v___y_130_ = v___x_138_;
goto v___jp_129_;
}
else
{
uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = 255;
v___x_140_ = lean_uint32_dec_le(v_c_123_, v___x_139_);
v___y_130_ = v___x_140_;
goto v___jp_129_;
}
}
else
{
return v___y_136_;
}
}
v___jp_141_:
{
if (v___y_142_ == 0)
{
uint32_t v___x_143_; uint8_t v___x_144_; 
v___x_143_ = 119964;
v___x_144_ = lean_uint32_dec_le(v___x_143_, v_c_123_);
if (v___x_144_ == 0)
{
v___y_136_ = v___x_144_;
goto v___jp_135_;
}
else
{
uint32_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = 120223;
v___x_146_ = lean_uint32_dec_le(v_c_123_, v___x_145_);
v___y_136_ = v___x_146_;
goto v___jp_135_;
}
}
else
{
return v___y_142_;
}
}
v___jp_147_:
{
if (v___y_148_ == 0)
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 8448;
v___x_150_ = lean_uint32_dec_le(v___x_149_, v_c_123_);
if (v___x_150_ == 0)
{
v___y_142_ = v___x_150_;
goto v___jp_141_;
}
else
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 8527;
v___x_152_ = lean_uint32_dec_le(v_c_123_, v___x_151_);
v___y_142_ = v___x_152_;
goto v___jp_141_;
}
}
else
{
return v___y_148_;
}
}
v___jp_153_:
{
if (v___y_154_ == 0)
{
uint32_t v___x_155_; uint8_t v___x_156_; 
v___x_155_ = 7936;
v___x_156_ = lean_uint32_dec_le(v___x_155_, v_c_123_);
if (v___x_156_ == 0)
{
v___y_148_ = v___x_156_;
goto v___jp_147_;
}
else
{
uint32_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 8190;
v___x_158_ = lean_uint32_dec_le(v_c_123_, v___x_157_);
v___y_148_ = v___x_158_;
goto v___jp_147_;
}
}
else
{
return v___y_154_;
}
}
v___jp_159_:
{
uint32_t v___x_160_; uint8_t v___x_161_; 
v___x_160_ = 970;
v___x_161_ = lean_uint32_dec_le(v___x_160_, v_c_123_);
if (v___x_161_ == 0)
{
v___y_154_ = v___x_161_;
goto v___jp_153_;
}
else
{
uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 1019;
v___x_163_ = lean_uint32_dec_le(v_c_123_, v___x_162_);
v___y_154_ = v___x_163_;
goto v___jp_153_;
}
}
v___jp_164_:
{
if (v___y_165_ == 0)
{
goto v___jp_159_;
}
else
{
uint32_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = 928;
v___x_167_ = lean_uint32_dec_eq(v_c_123_, v___x_166_);
if (v___x_167_ == 0)
{
uint32_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = 931;
v___x_169_ = lean_uint32_dec_eq(v_c_123_, v___x_168_);
if (v___x_169_ == 0)
{
return v___y_165_;
}
else
{
goto v___jp_159_;
}
}
else
{
goto v___jp_159_;
}
}
}
v___jp_170_:
{
uint32_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = 913;
v___x_172_ = lean_uint32_dec_le(v___x_171_, v_c_123_);
if (v___x_172_ == 0)
{
v___y_165_ = v___x_172_;
goto v___jp_164_;
}
else
{
uint32_t v___x_173_; uint8_t v___x_174_; 
v___x_173_ = 937;
v___x_174_ = lean_uint32_dec_le(v_c_123_, v___x_173_);
v___y_165_ = v___x_174_;
goto v___jp_164_;
}
}
v___jp_175_:
{
if (v___y_176_ == 0)
{
goto v___jp_170_;
}
else
{
uint32_t v___x_177_; uint8_t v___x_178_; 
v___x_177_ = 955;
v___x_178_ = lean_uint32_dec_eq(v_c_123_, v___x_177_);
if (v___x_178_ == 0)
{
return v___y_176_;
}
else
{
goto v___jp_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLetterLike___boxed(lean_object* v_c_183_){
_start:
{
uint32_t v_c_boxed_184_; uint8_t v_res_185_; lean_object* v_r_186_; 
v_c_boxed_184_ = lean_unbox_uint32(v_c_183_);
lean_dec(v_c_183_);
v_res_185_ = l_Lean_isLetterLike(v_c_boxed_184_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNumericSubscript(uint32_t v_c_187_){
_start:
{
uint32_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = 8320;
v___x_189_ = lean_uint32_dec_le(v___x_188_, v_c_187_);
if (v___x_189_ == 0)
{
return v___x_189_;
}
else
{
uint32_t v___x_190_; uint8_t v___x_191_; 
v___x_190_ = 8329;
v___x_191_ = lean_uint32_dec_le(v_c_187_, v___x_190_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNumericSubscript___boxed(lean_object* v_c_192_){
_start:
{
uint32_t v_c_boxed_193_; uint8_t v_res_194_; lean_object* v_r_195_; 
v_c_boxed_193_ = lean_unbox_uint32(v_c_192_);
lean_dec(v_c_192_);
v_res_194_ = l_Lean_isNumericSubscript(v_c_boxed_193_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT uint8_t l_Lean_isSubScriptAlnum(uint32_t v_c_196_){
_start:
{
uint8_t v___y_198_; uint8_t v___y_202_; uint8_t v___y_208_; uint32_t v___x_213_; uint8_t v___x_214_; 
v___x_213_ = 8320;
v___x_214_ = lean_uint32_dec_le(v___x_213_, v_c_196_);
if (v___x_214_ == 0)
{
v___y_208_ = v___x_214_;
goto v___jp_207_;
}
else
{
uint32_t v___x_215_; uint8_t v___x_216_; 
v___x_215_ = 8329;
v___x_216_ = lean_uint32_dec_le(v_c_196_, v___x_215_);
v___y_208_ = v___x_216_;
goto v___jp_207_;
}
v___jp_197_:
{
if (v___y_198_ == 0)
{
uint32_t v___x_199_; uint8_t v___x_200_; 
v___x_199_ = 11388;
v___x_200_ = lean_uint32_dec_eq(v_c_196_, v___x_199_);
return v___x_200_;
}
else
{
return v___y_198_;
}
}
v___jp_201_:
{
if (v___y_202_ == 0)
{
uint32_t v___x_203_; uint8_t v___x_204_; 
v___x_203_ = 7522;
v___x_204_ = lean_uint32_dec_le(v___x_203_, v_c_196_);
if (v___x_204_ == 0)
{
v___y_198_ = v___x_204_;
goto v___jp_197_;
}
else
{
uint32_t v___x_205_; uint8_t v___x_206_; 
v___x_205_ = 7530;
v___x_206_ = lean_uint32_dec_le(v_c_196_, v___x_205_);
v___y_198_ = v___x_206_;
goto v___jp_197_;
}
}
else
{
return v___y_202_;
}
}
v___jp_207_:
{
if (v___y_208_ == 0)
{
uint32_t v___x_209_; uint8_t v___x_210_; 
v___x_209_ = 8336;
v___x_210_ = lean_uint32_dec_le(v___x_209_, v_c_196_);
if (v___x_210_ == 0)
{
v___y_202_ = v___x_210_;
goto v___jp_201_;
}
else
{
uint32_t v___x_211_; uint8_t v___x_212_; 
v___x_211_ = 8348;
v___x_212_ = lean_uint32_dec_le(v_c_196_, v___x_211_);
v___y_202_ = v___x_212_;
goto v___jp_201_;
}
}
else
{
return v___y_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object* v_c_217_){
_start:
{
uint32_t v_c_boxed_218_; uint8_t v_res_219_; lean_object* v_r_220_; 
v_c_boxed_218_ = lean_unbox_uint32(v_c_217_);
lean_dec(v_c_217_);
v_res_219_ = l_Lean_isSubScriptAlnum(v_c_boxed_218_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirst(uint32_t v_c_221_){
_start:
{
uint8_t v___y_223_; uint32_t v___x_232_; uint8_t v___x_233_; 
v___x_232_ = 65;
v___x_233_ = lean_uint32_dec_le(v___x_232_, v_c_221_);
if (v___x_233_ == 0)
{
goto v___jp_227_;
}
else
{
uint32_t v___x_234_; uint8_t v___x_235_; 
v___x_234_ = 90;
v___x_235_ = lean_uint32_dec_le(v_c_221_, v___x_234_);
if (v___x_235_ == 0)
{
goto v___jp_227_;
}
else
{
return v___x_235_;
}
}
v___jp_222_:
{
if (v___y_223_ == 0)
{
uint32_t v___x_224_; uint8_t v___x_225_; 
v___x_224_ = 95;
v___x_225_ = lean_uint32_dec_eq(v_c_221_, v___x_224_);
if (v___x_225_ == 0)
{
uint8_t v___x_226_; 
v___x_226_ = l_Lean_isLetterLike(v_c_221_);
return v___x_226_;
}
else
{
return v___x_225_;
}
}
else
{
return v___y_223_;
}
}
v___jp_227_:
{
uint32_t v___x_228_; uint8_t v___x_229_; 
v___x_228_ = 97;
v___x_229_ = lean_uint32_dec_le(v___x_228_, v_c_221_);
if (v___x_229_ == 0)
{
v___y_223_ = v___x_229_;
goto v___jp_222_;
}
else
{
uint32_t v___x_230_; uint8_t v___x_231_; 
v___x_230_ = 122;
v___x_231_ = lean_uint32_dec_le(v_c_221_, v___x_230_);
v___y_223_ = v___x_231_;
goto v___jp_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirst___boxed(lean_object* v_c_236_){
_start:
{
uint32_t v_c_boxed_237_; uint8_t v_res_238_; lean_object* v_r_239_; 
v_c_boxed_237_ = lean_unbox_uint32(v_c_236_);
lean_dec(v_c_236_);
v_res_238_ = l_Lean_isIdFirst(v_c_boxed_237_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0(void){
_start:
{
uint32_t v___x_240_; uint8_t v___x_241_; 
v___x_240_ = 65;
v___x_241_ = lean_uint32_to_uint8(v___x_240_);
return v___x_241_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1(void){
_start:
{
uint32_t v___x_242_; uint8_t v___x_243_; 
v___x_242_ = 90;
v___x_243_ = lean_uint32_to_uint8(v___x_242_);
return v___x_243_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2(void){
_start:
{
uint32_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 97;
v___x_245_ = lean_uint32_to_uint8(v___x_244_);
return v___x_245_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3(void){
_start:
{
uint32_t v___x_246_; uint8_t v___x_247_; 
v___x_246_ = 122;
v___x_247_ = lean_uint32_to_uint8(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t v_c_248_){
_start:
{
uint8_t v___y_250_; uint8_t v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_256_ = lean_uint8_dec_le(v___x_255_, v_c_248_);
if (v___x_256_ == 0)
{
v___y_250_ = v___x_256_;
goto v___jp_249_;
}
else
{
uint8_t v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_258_ = lean_uint8_dec_le(v_c_248_, v___x_257_);
v___y_250_ = v___x_258_;
goto v___jp_249_;
}
v___jp_249_:
{
if (v___y_250_ == 0)
{
uint8_t v___x_251_; uint8_t v___x_252_; 
v___x_251_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_252_ = lean_uint8_dec_le(v___x_251_, v_c_248_);
if (v___x_252_ == 0)
{
return v___x_252_;
}
else
{
uint8_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_254_ = lean_uint8_dec_le(v_c_248_, v___x_253_);
return v___x_254_;
}
}
else
{
return v___y_250_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object* v_c_259_){
_start:
{
uint8_t v_c_boxed_260_; uint8_t v_res_261_; lean_object* v_r_262_; 
v_c_boxed_260_ = lean_unbox(v_c_259_);
v_res_261_ = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(v_c_boxed_260_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
static uint8_t _init_l_Lean_isIdFirstAscii___closed__0(void){
_start:
{
uint32_t v___x_263_; uint8_t v___x_264_; 
v___x_263_ = 95;
v___x_264_ = lean_uint32_to_uint8(v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirstAscii(uint8_t v_c_265_){
_start:
{
uint8_t v___y_267_; uint8_t v___y_271_; uint8_t v___x_276_; uint8_t v___x_277_; 
v___x_276_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_277_ = lean_uint8_dec_le(v___x_276_, v_c_265_);
if (v___x_277_ == 0)
{
v___y_271_ = v___x_277_;
goto v___jp_270_;
}
else
{
uint8_t v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_279_ = lean_uint8_dec_le(v_c_265_, v___x_278_);
v___y_271_ = v___x_279_;
goto v___jp_270_;
}
v___jp_266_:
{
if (v___y_267_ == 0)
{
uint8_t v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_269_ = lean_uint8_dec_eq(v_c_265_, v___x_268_);
return v___x_269_;
}
else
{
return v___y_267_;
}
}
v___jp_270_:
{
if (v___y_271_ == 0)
{
uint8_t v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_273_ = lean_uint8_dec_le(v___x_272_, v_c_265_);
if (v___x_273_ == 0)
{
v___y_267_ = v___x_273_;
goto v___jp_266_;
}
else
{
uint8_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_275_ = lean_uint8_dec_le(v_c_265_, v___x_274_);
v___y_267_ = v___x_275_;
goto v___jp_266_;
}
}
else
{
return v___y_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object* v_c_280_){
_start:
{
uint8_t v_c_boxed_281_; uint8_t v_res_282_; lean_object* v_r_283_; 
v_c_boxed_281_ = lean_unbox(v_c_280_);
v_res_282_ = l_Lean_isIdFirstAscii(v_c_boxed_281_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0(void){
_start:
{
uint32_t v___x_284_; uint8_t v___x_285_; 
v___x_284_ = 48;
v___x_285_ = lean_uint32_to_uint8(v___x_284_);
return v___x_285_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1(void){
_start:
{
uint32_t v___x_286_; uint8_t v___x_287_; 
v___x_286_ = 57;
v___x_287_ = lean_uint32_to_uint8(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t v_c_288_){
_start:
{
uint8_t v___y_290_; uint8_t v___y_296_; uint8_t v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_302_ = lean_uint8_dec_le(v___x_301_, v_c_288_);
if (v___x_302_ == 0)
{
v___y_296_ = v___x_302_;
goto v___jp_295_;
}
else
{
uint8_t v___x_303_; uint8_t v___x_304_; 
v___x_303_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_304_ = lean_uint8_dec_le(v_c_288_, v___x_303_);
v___y_296_ = v___x_304_;
goto v___jp_295_;
}
v___jp_289_:
{
if (v___y_290_ == 0)
{
uint8_t v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_292_ = lean_uint8_dec_le(v___x_291_, v_c_288_);
if (v___x_292_ == 0)
{
return v___x_292_;
}
else
{
uint8_t v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_294_ = lean_uint8_dec_le(v_c_288_, v___x_293_);
return v___x_294_;
}
}
else
{
return v___y_290_;
}
}
v___jp_295_:
{
if (v___y_296_ == 0)
{
uint8_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_298_ = lean_uint8_dec_le(v___x_297_, v_c_288_);
if (v___x_298_ == 0)
{
v___y_290_ = v___x_298_;
goto v___jp_289_;
}
else
{
uint8_t v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_300_ = lean_uint8_dec_le(v_c_288_, v___x_299_);
v___y_290_ = v___x_300_;
goto v___jp_289_;
}
}
else
{
return v___y_296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object* v_c_305_){
_start:
{
uint8_t v_c_boxed_306_; uint8_t v_res_307_; lean_object* v_r_308_; 
v_c_boxed_306_ = lean_unbox(v_c_305_);
v_res_307_ = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(v_c_boxed_306_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRest(uint32_t v_c_309_){
_start:
{
uint8_t v___y_311_; uint8_t v___y_323_; uint32_t v___x_333_; uint8_t v___x_334_; 
v___x_333_ = 65;
v___x_334_ = lean_uint32_dec_le(v___x_333_, v_c_309_);
if (v___x_334_ == 0)
{
goto v___jp_328_;
}
else
{
uint32_t v___x_335_; uint8_t v___x_336_; 
v___x_335_ = 90;
v___x_336_ = lean_uint32_dec_le(v_c_309_, v___x_335_);
if (v___x_336_ == 0)
{
goto v___jp_328_;
}
else
{
return v___x_336_;
}
}
v___jp_310_:
{
if (v___y_311_ == 0)
{
uint32_t v___x_312_; uint8_t v___x_313_; 
v___x_312_ = 95;
v___x_313_ = lean_uint32_dec_eq(v_c_309_, v___x_312_);
if (v___x_313_ == 0)
{
uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = 39;
v___x_315_ = lean_uint32_dec_eq(v_c_309_, v___x_314_);
if (v___x_315_ == 0)
{
uint32_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 33;
v___x_317_ = lean_uint32_dec_eq(v_c_309_, v___x_316_);
if (v___x_317_ == 0)
{
uint32_t v___x_318_; uint8_t v___x_319_; 
v___x_318_ = 63;
v___x_319_ = lean_uint32_dec_eq(v_c_309_, v___x_318_);
if (v___x_319_ == 0)
{
uint8_t v___x_320_; 
v___x_320_ = l_Lean_isLetterLike(v_c_309_);
if (v___x_320_ == 0)
{
uint8_t v___x_321_; 
v___x_321_ = l_Lean_isSubScriptAlnum(v_c_309_);
return v___x_321_;
}
else
{
return v___x_320_;
}
}
else
{
return v___x_319_;
}
}
else
{
return v___x_317_;
}
}
else
{
return v___x_315_;
}
}
else
{
return v___x_313_;
}
}
else
{
return v___y_311_;
}
}
v___jp_322_:
{
if (v___y_323_ == 0)
{
uint32_t v___x_324_; uint8_t v___x_325_; 
v___x_324_ = 48;
v___x_325_ = lean_uint32_dec_le(v___x_324_, v_c_309_);
if (v___x_325_ == 0)
{
v___y_311_ = v___x_325_;
goto v___jp_310_;
}
else
{
uint32_t v___x_326_; uint8_t v___x_327_; 
v___x_326_ = 57;
v___x_327_ = lean_uint32_dec_le(v_c_309_, v___x_326_);
v___y_311_ = v___x_327_;
goto v___jp_310_;
}
}
else
{
return v___y_323_;
}
}
v___jp_328_:
{
uint32_t v___x_329_; uint8_t v___x_330_; 
v___x_329_ = 97;
v___x_330_ = lean_uint32_dec_le(v___x_329_, v_c_309_);
if (v___x_330_ == 0)
{
v___y_323_ = v___x_330_;
goto v___jp_322_;
}
else
{
uint32_t v___x_331_; uint8_t v___x_332_; 
v___x_331_ = 122;
v___x_332_ = lean_uint32_dec_le(v_c_309_, v___x_331_);
v___y_323_ = v___x_332_;
goto v___jp_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object* v_c_337_){
_start:
{
uint32_t v_c_boxed_338_; uint8_t v_res_339_; lean_object* v_r_340_; 
v_c_boxed_338_ = lean_unbox_uint32(v_c_337_);
lean_dec(v_c_337_);
v_res_339_ = l_Lean_isIdRest(v_c_boxed_338_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__0(void){
_start:
{
uint32_t v___x_341_; uint8_t v___x_342_; 
v___x_341_ = 39;
v___x_342_ = lean_uint32_to_uint8(v___x_341_);
return v___x_342_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__1(void){
_start:
{
uint32_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 33;
v___x_344_ = lean_uint32_to_uint8(v___x_343_);
return v___x_344_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__2(void){
_start:
{
uint32_t v___x_345_; uint8_t v___x_346_; 
v___x_345_ = 63;
v___x_346_ = lean_uint32_to_uint8(v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRestAscii(uint8_t v_c_347_){
_start:
{
uint8_t v___y_349_; uint8_t v___y_359_; uint8_t v___y_365_; uint8_t v___x_370_; uint8_t v___x_371_; 
v___x_370_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_371_ = lean_uint8_dec_le(v___x_370_, v_c_347_);
if (v___x_371_ == 0)
{
v___y_365_ = v___x_371_;
goto v___jp_364_;
}
else
{
uint8_t v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_373_ = lean_uint8_dec_le(v_c_347_, v___x_372_);
v___y_365_ = v___x_373_;
goto v___jp_364_;
}
v___jp_348_:
{
if (v___y_349_ == 0)
{
uint8_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_351_ = lean_uint8_dec_eq(v_c_347_, v___x_350_);
if (v___x_351_ == 0)
{
uint8_t v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__0, &l_Lean_isIdRestAscii___closed__0_once, _init_l_Lean_isIdRestAscii___closed__0);
v___x_353_ = lean_uint8_dec_eq(v_c_347_, v___x_352_);
if (v___x_353_ == 0)
{
uint8_t v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__1, &l_Lean_isIdRestAscii___closed__1_once, _init_l_Lean_isIdRestAscii___closed__1);
v___x_355_ = lean_uint8_dec_eq(v_c_347_, v___x_354_);
if (v___x_355_ == 0)
{
uint8_t v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__2, &l_Lean_isIdRestAscii___closed__2_once, _init_l_Lean_isIdRestAscii___closed__2);
v___x_357_ = lean_uint8_dec_eq(v_c_347_, v___x_356_);
return v___x_357_;
}
else
{
return v___x_355_;
}
}
else
{
return v___x_353_;
}
}
else
{
return v___x_351_;
}
}
else
{
return v___y_349_;
}
}
v___jp_358_:
{
if (v___y_359_ == 0)
{
uint8_t v___x_360_; uint8_t v___x_361_; 
v___x_360_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_361_ = lean_uint8_dec_le(v___x_360_, v_c_347_);
if (v___x_361_ == 0)
{
v___y_349_ = v___x_361_;
goto v___jp_348_;
}
else
{
uint8_t v___x_362_; uint8_t v___x_363_; 
v___x_362_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_363_ = lean_uint8_dec_le(v_c_347_, v___x_362_);
v___y_349_ = v___x_363_;
goto v___jp_348_;
}
}
else
{
return v___y_359_;
}
}
v___jp_364_:
{
if (v___y_365_ == 0)
{
uint8_t v___x_366_; uint8_t v___x_367_; 
v___x_366_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_367_ = lean_uint8_dec_le(v___x_366_, v_c_347_);
if (v___x_367_ == 0)
{
v___y_359_ = v___x_367_;
goto v___jp_358_;
}
else
{
uint8_t v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_369_ = lean_uint8_dec_le(v_c_347_, v___x_368_);
v___y_359_ = v___x_369_;
goto v___jp_358_;
}
}
else
{
return v___y_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRestAscii___boxed(lean_object* v_c_374_){
_start:
{
uint8_t v_c_boxed_375_; uint8_t v_res_376_; lean_object* v_r_377_; 
v_c_boxed_375_ = lean_unbox(v_c_374_);
v_res_376_ = l_Lean_isIdRestAscii(v_c_boxed_375_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
static uint32_t _init_l_Lean_idBeginEscape(void){
_start:
{
uint32_t v___x_378_; 
v___x_378_ = 171;
return v___x_378_;
}
}
static uint32_t _init_l_Lean_idEndEscape(void){
_start:
{
uint32_t v___x_379_; 
v___x_379_ = 187;
return v___x_379_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdBeginEscape(uint32_t v_c_380_){
_start:
{
uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = 171;
v___x_382_ = lean_uint32_dec_eq(v_c_380_, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdBeginEscape___boxed(lean_object* v_c_383_){
_start:
{
uint32_t v_c_boxed_384_; uint8_t v_res_385_; lean_object* v_r_386_; 
v_c_boxed_384_ = lean_unbox_uint32(v_c_383_);
lean_dec(v_c_383_);
v_res_385_ = l_Lean_isIdBeginEscape(v_c_boxed_384_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdEndEscape(uint32_t v_c_387_){
_start:
{
uint32_t v___x_388_; uint8_t v___x_389_; 
v___x_388_ = 187;
v___x_389_ = lean_uint32_dec_eq(v_c_387_, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdEndEscape___boxed(lean_object* v_c_390_){
_start:
{
uint32_t v_c_boxed_391_; uint8_t v_res_392_; lean_object* v_r_393_; 
v_c_boxed_391_ = lean_unbox_uint32(v_c_390_);
lean_dec(v_c_390_);
v_res_392_ = l_Lean_isIdEndEscape(v_c_boxed_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot(lean_object* v_x_394_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
return v_x_394_;
}
else
{
lean_object* v_pre_395_; 
v_pre_395_ = lean_ctor_get(v_x_394_, 0);
if (lean_obj_tag(v_pre_395_) == 0)
{
lean_inc(v_x_394_);
return v_x_394_;
}
else
{
v_x_394_ = v_pre_395_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot___boxed(lean_object* v_x_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Name_getRoot(v_x_397_);
lean_dec(v_x_397_);
return v_res_398_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInaccessibleUserName(lean_object* v_x_400_){
_start:
{
switch(lean_obj_tag(v_x_400_))
{
case 1:
{
lean_object* v_str_401_; uint32_t v___x_402_; uint8_t v___x_403_; 
v_str_401_ = lean_ctor_get(v_x_400_, 1);
lean_inc_ref_n(v_str_401_, 2);
lean_dec_ref_known(v_x_400_, 2);
v___x_402_ = 10013;
v___x_403_ = lean_string_contains(v_str_401_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_Name_isInaccessibleUserName___closed__0));
v___x_405_ = lean_string_dec_eq(v_str_401_, v___x_404_);
lean_dec_ref(v_str_401_);
return v___x_405_;
}
else
{
lean_dec_ref(v_str_401_);
return v___x_403_;
}
}
case 2:
{
lean_object* v_pre_406_; 
v_pre_406_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_pre_406_);
lean_dec_ref_known(v_x_400_, 2);
v_x_400_ = v_pre_406_;
goto _start;
}
default: 
{
uint8_t v___x_408_; 
lean_dec(v_x_400_);
v___x_408_ = 0;
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInaccessibleUserName___boxed(lean_object* v_x_409_){
_start:
{
uint8_t v_res_410_; lean_object* v_r_411_; 
v_res_410_ = l_Lean_Name_isInaccessibleUserName(v_x_409_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(lean_object* v_s_412_, lean_object* v_i_413_){
_start:
{
uint8_t v___y_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = lean_string_utf8_byte_size(v_s_412_);
v___x_421_ = lean_nat_dec_lt(v_i_413_, v___x_420_);
if (v___x_421_ == 0)
{
uint8_t v___x_422_; 
lean_dec(v_i_413_);
v___x_422_ = 1;
return v___x_422_;
}
else
{
uint8_t v_c_423_; uint8_t v___y_425_; uint8_t v___y_435_; uint8_t v___y_441_; uint8_t v___x_446_; uint8_t v___x_447_; 
lean_inc(v_i_413_);
v_c_423_ = lean_string_get_byte_fast(v_s_412_, v_i_413_);
v___x_446_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_447_ = lean_uint8_dec_le(v___x_446_, v_c_423_);
if (v___x_447_ == 0)
{
v___y_441_ = v___x_447_;
goto v___jp_440_;
}
else
{
uint8_t v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_449_ = lean_uint8_dec_le(v_c_423_, v___x_448_);
v___y_441_ = v___x_449_;
goto v___jp_440_;
}
v___jp_424_:
{
if (v___y_425_ == 0)
{
uint8_t v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_427_ = lean_uint8_dec_eq(v_c_423_, v___x_426_);
if (v___x_427_ == 0)
{
uint8_t v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__0, &l_Lean_isIdRestAscii___closed__0_once, _init_l_Lean_isIdRestAscii___closed__0);
v___x_429_ = lean_uint8_dec_eq(v_c_423_, v___x_428_);
if (v___x_429_ == 0)
{
uint8_t v___x_430_; uint8_t v___x_431_; 
v___x_430_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__1, &l_Lean_isIdRestAscii___closed__1_once, _init_l_Lean_isIdRestAscii___closed__1);
v___x_431_ = lean_uint8_dec_eq(v_c_423_, v___x_430_);
if (v___x_431_ == 0)
{
uint8_t v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__2, &l_Lean_isIdRestAscii___closed__2_once, _init_l_Lean_isIdRestAscii___closed__2);
v___x_433_ = lean_uint8_dec_eq(v_c_423_, v___x_432_);
v___y_419_ = v___x_433_;
goto v___jp_418_;
}
else
{
v___y_419_ = v___x_431_;
goto v___jp_418_;
}
}
else
{
v___y_419_ = v___x_429_;
goto v___jp_418_;
}
}
else
{
v___y_419_ = v___x_427_;
goto v___jp_418_;
}
}
else
{
goto v___jp_414_;
}
}
v___jp_434_:
{
if (v___y_435_ == 0)
{
uint8_t v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_437_ = lean_uint8_dec_le(v___x_436_, v_c_423_);
if (v___x_437_ == 0)
{
v___y_425_ = v___x_437_;
goto v___jp_424_;
}
else
{
uint8_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_439_ = lean_uint8_dec_le(v_c_423_, v___x_438_);
v___y_425_ = v___x_439_;
goto v___jp_424_;
}
}
else
{
goto v___jp_414_;
}
}
v___jp_440_:
{
if (v___y_441_ == 0)
{
uint8_t v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_443_ = lean_uint8_dec_le(v___x_442_, v_c_423_);
if (v___x_443_ == 0)
{
v___y_435_ = v___x_443_;
goto v___jp_434_;
}
else
{
uint8_t v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_445_ = lean_uint8_dec_le(v_c_423_, v___x_444_);
v___y_435_ = v___x_445_;
goto v___jp_434_;
}
}
else
{
goto v___jp_414_;
}
}
}
v___jp_414_:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = lean_nat_add(v_i_413_, v___x_415_);
lean_dec(v_i_413_);
v_i_413_ = v___x_416_;
goto _start;
}
v___jp_418_:
{
if (v___y_419_ == 0)
{
lean_dec(v_i_413_);
return v___y_419_;
}
else
{
goto v___jp_414_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object* v_s_450_, lean_object* v_i_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_450_, v_i_451_);
lean_dec_ref(v_s_450_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object* v_s_454_){
_start:
{
lean_object* v___x_458_; uint8_t v_c_459_; uint8_t v___y_461_; uint8_t v___y_465_; uint8_t v___x_470_; uint8_t v___x_471_; 
v___x_458_ = lean_unsigned_to_nat(0u);
v_c_459_ = lean_string_get_byte_fast(v_s_454_, v___x_458_);
v___x_470_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_471_ = lean_uint8_dec_le(v___x_470_, v_c_459_);
if (v___x_471_ == 0)
{
v___y_465_ = v___x_471_;
goto v___jp_464_;
}
else
{
uint8_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_473_ = lean_uint8_dec_le(v_c_459_, v___x_472_);
v___y_465_ = v___x_473_;
goto v___jp_464_;
}
v___jp_455_:
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_454_, v___x_456_);
return v___x_457_;
}
v___jp_460_:
{
if (v___y_461_ == 0)
{
uint8_t v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_463_ = lean_uint8_dec_eq(v_c_459_, v___x_462_);
if (v___x_463_ == 0)
{
return v___x_463_;
}
else
{
goto v___jp_455_;
}
}
else
{
goto v___jp_455_;
}
}
v___jp_464_:
{
if (v___y_465_ == 0)
{
uint8_t v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_467_ = lean_uint8_dec_le(v___x_466_, v_c_459_);
if (v___x_467_ == 0)
{
v___y_461_ = v___x_467_;
goto v___jp_460_;
}
else
{
uint8_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_469_ = lean_uint8_dec_le(v_c_459_, v___x_468_);
v___y_461_ = v___x_469_;
goto v___jp_460_;
}
}
else
{
goto v___jp_455_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object* v_s_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_474_);
lean_dec_ref(v_s_474_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(lean_object* v_s_477_, lean_object* v_h_478_){
_start:
{
lean_object* v___x_482_; uint8_t v_c_483_; uint8_t v___y_485_; uint8_t v___y_489_; uint8_t v___x_494_; uint8_t v___x_495_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v_c_483_ = lean_string_get_byte_fast(v_s_477_, v___x_482_);
v___x_494_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_495_ = lean_uint8_dec_le(v___x_494_, v_c_483_);
if (v___x_495_ == 0)
{
v___y_489_ = v___x_495_;
goto v___jp_488_;
}
else
{
uint8_t v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_497_ = lean_uint8_dec_le(v_c_483_, v___x_496_);
v___y_489_ = v___x_497_;
goto v___jp_488_;
}
v___jp_479_:
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_477_, v___x_480_);
return v___x_481_;
}
v___jp_484_:
{
if (v___y_485_ == 0)
{
uint8_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_487_ = lean_uint8_dec_eq(v_c_483_, v___x_486_);
if (v___x_487_ == 0)
{
return v___x_487_;
}
else
{
goto v___jp_479_;
}
}
else
{
goto v___jp_479_;
}
}
v___jp_488_:
{
if (v___y_489_ == 0)
{
uint8_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_491_ = lean_uint8_dec_le(v___x_490_, v_c_483_);
if (v___x_491_ == 0)
{
v___y_485_ = v___x_491_;
goto v___jp_484_;
}
else
{
uint8_t v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_493_ = lean_uint8_dec_le(v_c_483_, v___x_492_);
v___y_485_ = v___x_493_;
goto v___jp_484_;
}
}
else
{
goto v___jp_479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object* v_s_498_, lean_object* v_h_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(v_s_498_, v_h_499_);
lean_dec_ref(v_s_498_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(lean_object* v_s_503_){
_start:
{
uint8_t v___y_513_; uint32_t v___y_515_; uint8_t v___y_516_; uint32_t v___y_521_; uint8_t v___y_527_; lean_object* v___x_537_; uint8_t v_c_538_; uint8_t v___y_540_; uint8_t v___y_544_; uint8_t v___x_549_; uint8_t v___x_550_; 
v___x_537_ = lean_unsigned_to_nat(0u);
v_c_538_ = lean_string_get_byte_fast(v_s_503_, v___x_537_);
v___x_549_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_550_ = lean_uint8_dec_le(v___x_549_, v_c_538_);
if (v___x_550_ == 0)
{
v___y_544_ = v___x_550_;
goto v___jp_543_;
}
else
{
uint8_t v___x_551_; uint8_t v___x_552_; 
v___x_551_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_552_ = lean_uint8_dec_le(v_c_538_, v___x_551_);
v___y_544_ = v___x_552_;
goto v___jp_543_;
}
v___jp_504_:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_string_utf8_byte_size(v_s_503_);
v___x_507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_507_, 0, v_s_503_);
lean_ctor_set(v___x_507_, 1, v___x_505_);
lean_ctor_set(v___x_507_, 2, v___x_506_);
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_substring_drop(v___x_507_, v___x_508_);
v___x_510_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_511_ = lean_substring_all(v___x_509_, v___x_510_);
return v___x_511_;
}
v___jp_512_:
{
if (v___y_513_ == 0)
{
lean_dec_ref(v_s_503_);
return v___y_513_;
}
else
{
goto v___jp_504_;
}
}
v___jp_514_:
{
if (v___y_516_ == 0)
{
uint32_t v___x_517_; uint8_t v___x_518_; 
v___x_517_ = 95;
v___x_518_ = lean_uint32_dec_eq(v___y_515_, v___x_517_);
if (v___x_518_ == 0)
{
uint8_t v___x_519_; 
v___x_519_ = l_Lean_isLetterLike(v___y_515_);
v___y_513_ = v___x_519_;
goto v___jp_512_;
}
else
{
v___y_513_ = v___x_518_;
goto v___jp_512_;
}
}
else
{
goto v___jp_504_;
}
}
v___jp_520_:
{
uint32_t v___x_522_; uint8_t v___x_523_; 
v___x_522_ = 97;
v___x_523_ = lean_uint32_dec_le(v___x_522_, v___y_521_);
if (v___x_523_ == 0)
{
v___y_515_ = v___y_521_;
v___y_516_ = v___x_523_;
goto v___jp_514_;
}
else
{
uint32_t v___x_524_; uint8_t v___x_525_; 
v___x_524_ = 122;
v___x_525_ = lean_uint32_dec_le(v___y_521_, v___x_524_);
v___y_515_ = v___y_521_;
v___y_516_ = v___x_525_;
goto v___jp_514_;
}
}
v___jp_526_:
{
if (v___y_527_ == 0)
{
lean_object* v___x_528_; uint32_t v___x_529_; uint32_t v___x_530_; uint8_t v___x_531_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_string_utf8_get(v_s_503_, v___x_528_);
v___x_530_ = 65;
v___x_531_ = lean_uint32_dec_le(v___x_530_, v___x_529_);
if (v___x_531_ == 0)
{
v___y_521_ = v___x_529_;
goto v___jp_520_;
}
else
{
uint32_t v___x_532_; uint8_t v___x_533_; 
v___x_532_ = 90;
v___x_533_ = lean_uint32_dec_le(v___x_529_, v___x_532_);
if (v___x_533_ == 0)
{
v___y_521_ = v___x_529_;
goto v___jp_520_;
}
else
{
goto v___jp_504_;
}
}
}
else
{
lean_dec_ref(v_s_503_);
return v___y_527_;
}
}
v___jp_534_:
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_503_, v___x_535_);
v___y_527_ = v___x_536_;
goto v___jp_526_;
}
v___jp_539_:
{
if (v___y_540_ == 0)
{
uint8_t v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_542_ = lean_uint8_dec_eq(v_c_538_, v___x_541_);
if (v___x_542_ == 0)
{
v___y_527_ = v___x_542_;
goto v___jp_526_;
}
else
{
goto v___jp_534_;
}
}
else
{
goto v___jp_534_;
}
}
v___jp_543_:
{
if (v___y_544_ == 0)
{
uint8_t v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_546_ = lean_uint8_dec_le(v___x_545_, v_c_538_);
if (v___x_546_ == 0)
{
v___y_540_ = v___x_546_;
goto v___jp_539_;
}
else
{
uint8_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_548_ = lean_uint8_dec_le(v_c_538_, v___x_547_);
v___y_540_ = v___x_548_;
goto v___jp_539_;
}
}
else
{
goto v___jp_534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(v_s_553_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(lean_object* v_s_556_, lean_object* v_h_557_){
_start:
{
uint8_t v___y_567_; uint32_t v___y_569_; uint8_t v___y_570_; uint32_t v___y_575_; uint8_t v___y_581_; lean_object* v___x_591_; uint8_t v_c_592_; uint8_t v___y_594_; uint8_t v___y_598_; uint8_t v___x_603_; uint8_t v___x_604_; 
v___x_591_ = lean_unsigned_to_nat(0u);
v_c_592_ = lean_string_get_byte_fast(v_s_556_, v___x_591_);
v___x_603_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_604_ = lean_uint8_dec_le(v___x_603_, v_c_592_);
if (v___x_604_ == 0)
{
v___y_598_ = v___x_604_;
goto v___jp_597_;
}
else
{
uint8_t v___x_605_; uint8_t v___x_606_; 
v___x_605_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_606_ = lean_uint8_dec_le(v_c_592_, v___x_605_);
v___y_598_ = v___x_606_;
goto v___jp_597_;
}
v___jp_558_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_string_utf8_byte_size(v_s_556_);
v___x_561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_561_, 0, v_s_556_);
lean_ctor_set(v___x_561_, 1, v___x_559_);
lean_ctor_set(v___x_561_, 2, v___x_560_);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_substring_drop(v___x_561_, v___x_562_);
v___x_564_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_565_ = lean_substring_all(v___x_563_, v___x_564_);
return v___x_565_;
}
v___jp_566_:
{
if (v___y_567_ == 0)
{
lean_dec_ref(v_s_556_);
return v___y_567_;
}
else
{
goto v___jp_558_;
}
}
v___jp_568_:
{
if (v___y_570_ == 0)
{
uint32_t v___x_571_; uint8_t v___x_572_; 
v___x_571_ = 95;
v___x_572_ = lean_uint32_dec_eq(v___y_569_, v___x_571_);
if (v___x_572_ == 0)
{
uint8_t v___x_573_; 
v___x_573_ = l_Lean_isLetterLike(v___y_569_);
v___y_567_ = v___x_573_;
goto v___jp_566_;
}
else
{
v___y_567_ = v___x_572_;
goto v___jp_566_;
}
}
else
{
goto v___jp_558_;
}
}
v___jp_574_:
{
uint32_t v___x_576_; uint8_t v___x_577_; 
v___x_576_ = 97;
v___x_577_ = lean_uint32_dec_le(v___x_576_, v___y_575_);
if (v___x_577_ == 0)
{
v___y_569_ = v___y_575_;
v___y_570_ = v___x_577_;
goto v___jp_568_;
}
else
{
uint32_t v___x_578_; uint8_t v___x_579_; 
v___x_578_ = 122;
v___x_579_ = lean_uint32_dec_le(v___y_575_, v___x_578_);
v___y_569_ = v___y_575_;
v___y_570_ = v___x_579_;
goto v___jp_568_;
}
}
v___jp_580_:
{
if (v___y_581_ == 0)
{
lean_object* v___x_582_; uint32_t v___x_583_; uint32_t v___x_584_; uint8_t v___x_585_; 
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_string_utf8_get(v_s_556_, v___x_582_);
v___x_584_ = 65;
v___x_585_ = lean_uint32_dec_le(v___x_584_, v___x_583_);
if (v___x_585_ == 0)
{
v___y_575_ = v___x_583_;
goto v___jp_574_;
}
else
{
uint32_t v___x_586_; uint8_t v___x_587_; 
v___x_586_ = 90;
v___x_587_ = lean_uint32_dec_le(v___x_583_, v___x_586_);
if (v___x_587_ == 0)
{
v___y_575_ = v___x_583_;
goto v___jp_574_;
}
else
{
goto v___jp_558_;
}
}
}
else
{
lean_dec_ref(v_s_556_);
return v___y_581_;
}
}
v___jp_588_:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_556_, v___x_589_);
v___y_581_ = v___x_590_;
goto v___jp_580_;
}
v___jp_593_:
{
if (v___y_594_ == 0)
{
uint8_t v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_596_ = lean_uint8_dec_eq(v_c_592_, v___x_595_);
if (v___x_596_ == 0)
{
v___y_581_ = v___x_596_;
goto v___jp_580_;
}
else
{
goto v___jp_588_;
}
}
else
{
goto v___jp_588_;
}
}
v___jp_597_:
{
if (v___y_598_ == 0)
{
uint8_t v___x_599_; uint8_t v___x_600_; 
v___x_599_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_600_ = lean_uint8_dec_le(v___x_599_, v_c_592_);
if (v___x_600_ == 0)
{
v___y_594_ = v___x_600_;
goto v___jp_593_;
}
else
{
uint8_t v___x_601_; uint8_t v___x_602_; 
v___x_601_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_602_ = lean_uint8_dec_le(v_c_592_, v___x_601_);
v___y_594_ = v___x_602_;
goto v___jp_593_;
}
}
else
{
goto v___jp_588_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_607_, lean_object* v_h_608_){
_start:
{
uint8_t v_res_609_; lean_object* v_r_610_; 
v_res_609_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(v_s_607_, v_h_608_);
v_r_610_ = lean_box(v_res_609_);
return v_r_610_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0(void){
_start:
{
uint32_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = 171;
v___x_612_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_613_ = lean_string_push(v___x_612_, v___x_611_);
return v___x_613_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1(void){
_start:
{
uint32_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = 187;
v___x_615_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_616_ = lean_string_push(v___x_615_, v___x_614_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape(lean_object* v_s_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_618_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_619_ = lean_string_append(v___x_618_, v_s_617_);
v___x_620_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_621_ = lean_string_append(v___x_619_, v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___boxed(lean_object* v_s_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l___private_Init_Meta_Defs_0__Lean_Name_escape(v_s_622_);
lean_dec_ref(v_s_622_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(lean_object* v_s_625_, uint8_t v_force_626_){
_start:
{
uint8_t v___y_637_; uint8_t v___y_648_; uint32_t v___y_650_; uint8_t v___y_651_; uint32_t v___y_656_; uint8_t v___y_662_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_string_utf8_byte_size(v_s_625_);
v___x_675_ = lean_nat_dec_lt(v___x_673_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_676_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_677_ = lean_string_append(v___x_676_, v_s_625_);
lean_dec_ref(v_s_625_);
v___x_678_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_679_ = lean_string_append(v___x_677_, v___x_678_);
v___x_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
else
{
uint8_t v___x_681_; 
v___x_681_ = lean_bool_not(v_force_626_);
if (v___x_681_ == 0)
{
v___y_637_ = v___x_681_;
goto v___jp_636_;
}
else
{
uint8_t v_c_682_; uint8_t v___y_684_; uint8_t v___y_688_; uint8_t v___x_693_; uint8_t v___x_694_; 
v_c_682_ = lean_string_get_byte_fast(v_s_625_, v___x_673_);
v___x_693_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_694_ = lean_uint8_dec_le(v___x_693_, v_c_682_);
if (v___x_694_ == 0)
{
v___y_688_ = v___x_694_;
goto v___jp_687_;
}
else
{
uint8_t v___x_695_; uint8_t v___x_696_; 
v___x_695_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_696_ = lean_uint8_dec_le(v_c_682_, v___x_695_);
v___y_688_ = v___x_696_;
goto v___jp_687_;
}
v___jp_683_:
{
if (v___y_684_ == 0)
{
uint8_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_686_ = lean_uint8_dec_eq(v_c_682_, v___x_685_);
if (v___x_686_ == 0)
{
v___y_662_ = v___x_686_;
goto v___jp_661_;
}
else
{
goto v___jp_670_;
}
}
else
{
goto v___jp_670_;
}
}
v___jp_687_:
{
if (v___y_688_ == 0)
{
uint8_t v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_690_ = lean_uint8_dec_le(v___x_689_, v_c_682_);
if (v___x_690_ == 0)
{
v___y_684_ = v___x_690_;
goto v___jp_683_;
}
else
{
uint8_t v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_692_ = lean_uint8_dec_le(v_c_682_, v___x_691_);
v___y_684_ = v___x_692_;
goto v___jp_683_;
}
}
else
{
goto v___jp_670_;
}
}
}
}
v___jp_627_:
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0));
lean_inc_ref(v_s_625_);
v___x_629_ = lean_string_any(v_s_625_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_630_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_631_ = lean_string_append(v___x_630_, v_s_625_);
lean_dec_ref(v_s_625_);
v___x_632_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_633_ = lean_string_append(v___x_631_, v___x_632_);
v___x_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; 
lean_dec_ref(v_s_625_);
v___x_635_ = lean_box(0);
return v___x_635_;
}
}
v___jp_636_:
{
if (v___y_637_ == 0)
{
goto v___jp_627_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v_s_625_);
return v___x_638_;
}
}
v___jp_639_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_string_utf8_byte_size(v_s_625_);
lean_inc_ref(v_s_625_);
v___x_642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_642_, 0, v_s_625_);
lean_ctor_set(v___x_642_, 1, v___x_640_);
lean_ctor_set(v___x_642_, 2, v___x_641_);
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_substring_drop(v___x_642_, v___x_643_);
v___x_645_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_646_ = lean_substring_all(v___x_644_, v___x_645_);
v___y_637_ = v___x_646_;
goto v___jp_636_;
}
v___jp_647_:
{
if (v___y_648_ == 0)
{
goto v___jp_627_;
}
else
{
goto v___jp_639_;
}
}
v___jp_649_:
{
if (v___y_651_ == 0)
{
uint32_t v___x_652_; uint8_t v___x_653_; 
v___x_652_ = 95;
v___x_653_ = lean_uint32_dec_eq(v___y_650_, v___x_652_);
if (v___x_653_ == 0)
{
uint8_t v___x_654_; 
v___x_654_ = l_Lean_isLetterLike(v___y_650_);
v___y_648_ = v___x_654_;
goto v___jp_647_;
}
else
{
v___y_648_ = v___x_653_;
goto v___jp_647_;
}
}
else
{
goto v___jp_639_;
}
}
v___jp_655_:
{
uint32_t v___x_657_; uint8_t v___x_658_; 
v___x_657_ = 97;
v___x_658_ = lean_uint32_dec_le(v___x_657_, v___y_656_);
if (v___x_658_ == 0)
{
v___y_650_ = v___y_656_;
v___y_651_ = v___x_658_;
goto v___jp_649_;
}
else
{
uint32_t v___x_659_; uint8_t v___x_660_; 
v___x_659_ = 122;
v___x_660_ = lean_uint32_dec_le(v___y_656_, v___x_659_);
v___y_650_ = v___y_656_;
v___y_651_ = v___x_660_;
goto v___jp_649_;
}
}
v___jp_661_:
{
if (v___y_662_ == 0)
{
lean_object* v___x_663_; uint32_t v___x_664_; uint32_t v___x_665_; uint8_t v___x_666_; 
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_string_utf8_get(v_s_625_, v___x_663_);
v___x_665_ = 65;
v___x_666_ = lean_uint32_dec_le(v___x_665_, v___x_664_);
if (v___x_666_ == 0)
{
v___y_656_ = v___x_664_;
goto v___jp_655_;
}
else
{
uint32_t v___x_667_; uint8_t v___x_668_; 
v___x_667_ = 90;
v___x_668_ = lean_uint32_dec_le(v___x_664_, v___x_667_);
if (v___x_668_ == 0)
{
v___y_656_ = v___x_664_;
goto v___jp_655_;
}
else
{
goto v___jp_639_;
}
}
}
else
{
lean_object* v___x_669_; 
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v_s_625_);
return v___x_669_;
}
}
v___jp_670_:
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_625_, v___x_671_);
v___y_662_ = v___x_672_;
goto v___jp_661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object* v_s_697_, lean_object* v_force_698_){
_start:
{
uint8_t v_force_boxed_699_; lean_object* v_res_700_; 
v_force_boxed_699_ = lean_unbox(v_force_698_);
v_res_700_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(v_s_697_, v_force_boxed_699_);
return v_res_700_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t v___y_701_){
_start:
{
uint32_t v___x_702_; uint8_t v___x_703_; 
v___x_702_ = 187;
v___x_703_ = lean_uint32_dec_eq(v___y_701_, v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object* v___y_704_){
_start:
{
uint32_t v___y_444__boxed_705_; uint8_t v_res_706_; lean_object* v_r_707_; 
v___y_444__boxed_705_ = lean_unbox_uint32(v___y_704_);
lean_dec(v___y_704_);
v_res_706_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(v___y_444__boxed_705_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t v___y_708_){
_start:
{
uint8_t v___y_710_; uint8_t v___y_722_; uint32_t v___x_732_; uint8_t v___x_733_; 
v___x_732_ = 65;
v___x_733_ = lean_uint32_dec_le(v___x_732_, v___y_708_);
if (v___x_733_ == 0)
{
goto v___jp_727_;
}
else
{
uint32_t v___x_734_; uint8_t v___x_735_; 
v___x_734_ = 90;
v___x_735_ = lean_uint32_dec_le(v___y_708_, v___x_734_);
if (v___x_735_ == 0)
{
goto v___jp_727_;
}
else
{
return v___x_735_;
}
}
v___jp_709_:
{
if (v___y_710_ == 0)
{
uint32_t v___x_711_; uint8_t v___x_712_; 
v___x_711_ = 95;
v___x_712_ = lean_uint32_dec_eq(v___y_708_, v___x_711_);
if (v___x_712_ == 0)
{
uint32_t v___x_713_; uint8_t v___x_714_; 
v___x_713_ = 39;
v___x_714_ = lean_uint32_dec_eq(v___y_708_, v___x_713_);
if (v___x_714_ == 0)
{
uint32_t v___x_715_; uint8_t v___x_716_; 
v___x_715_ = 33;
v___x_716_ = lean_uint32_dec_eq(v___y_708_, v___x_715_);
if (v___x_716_ == 0)
{
uint32_t v___x_717_; uint8_t v___x_718_; 
v___x_717_ = 63;
v___x_718_ = lean_uint32_dec_eq(v___y_708_, v___x_717_);
if (v___x_718_ == 0)
{
uint8_t v___x_719_; 
v___x_719_ = l_Lean_isLetterLike(v___y_708_);
if (v___x_719_ == 0)
{
uint8_t v___x_720_; 
v___x_720_ = l_Lean_isSubScriptAlnum(v___y_708_);
return v___x_720_;
}
else
{
return v___x_719_;
}
}
else
{
return v___x_718_;
}
}
else
{
return v___x_716_;
}
}
else
{
return v___x_714_;
}
}
else
{
return v___x_712_;
}
}
else
{
return v___y_710_;
}
}
v___jp_721_:
{
if (v___y_722_ == 0)
{
uint32_t v___x_723_; uint8_t v___x_724_; 
v___x_723_ = 48;
v___x_724_ = lean_uint32_dec_le(v___x_723_, v___y_708_);
if (v___x_724_ == 0)
{
v___y_710_ = v___x_724_;
goto v___jp_709_;
}
else
{
uint32_t v___x_725_; uint8_t v___x_726_; 
v___x_725_ = 57;
v___x_726_ = lean_uint32_dec_le(v___y_708_, v___x_725_);
v___y_710_ = v___x_726_;
goto v___jp_709_;
}
}
else
{
return v___y_722_;
}
}
v___jp_727_:
{
uint32_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 97;
v___x_729_ = lean_uint32_dec_le(v___x_728_, v___y_708_);
if (v___x_729_ == 0)
{
v___y_722_ = v___x_729_;
goto v___jp_721_;
}
else
{
uint32_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = 122;
v___x_731_ = lean_uint32_dec_le(v___y_708_, v___x_730_);
v___y_722_ = v___x_731_;
goto v___jp_721_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object* v___y_736_){
_start:
{
uint32_t v___y_451__boxed_737_; uint8_t v_res_738_; lean_object* v_r_739_; 
v___y_451__boxed_737_ = lean_unbox_uint32(v___y_736_);
lean_dec(v___y_736_);
v_res_738_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(v___y_451__boxed_737_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t v_escape_742_, lean_object* v_s_743_, uint8_t v_force_744_){
_start:
{
if (v_escape_742_ == 0)
{
return v_s_743_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_string_utf8_byte_size(v_s_743_);
v___x_747_ = lean_nat_dec_lt(v___x_745_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_748_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_749_ = lean_string_append(v___x_748_, v_s_743_);
lean_dec_ref(v_s_743_);
v___x_750_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_751_ = lean_string_append(v___x_749_, v___x_750_);
return v___x_751_;
}
else
{
lean_object* v___f_752_; uint8_t v___y_760_; uint8_t v___x_761_; 
v___f_752_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v___x_761_ = lean_bool_not(v_force_744_);
if (v___x_761_ == 0)
{
v___y_760_ = v___x_761_;
goto v___jp_759_;
}
else
{
lean_object* v___f_762_; uint8_t v___y_769_; uint32_t v___y_771_; uint8_t v___y_772_; uint32_t v___y_777_; uint8_t v___y_783_; uint8_t v_c_792_; uint8_t v___y_794_; uint8_t v___y_798_; uint8_t v___x_803_; uint8_t v___x_804_; 
v___f_762_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_792_ = lean_string_get_byte_fast(v_s_743_, v___x_745_);
v___x_803_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_804_ = lean_uint8_dec_le(v___x_803_, v_c_792_);
if (v___x_804_ == 0)
{
v___y_798_ = v___x_804_;
goto v___jp_797_;
}
else
{
uint8_t v___x_805_; uint8_t v___x_806_; 
v___x_805_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_806_ = lean_uint8_dec_le(v_c_792_, v___x_805_);
v___y_798_ = v___x_806_;
goto v___jp_797_;
}
v___jp_763_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
lean_inc_ref(v_s_743_);
v___x_764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_764_, 0, v_s_743_);
lean_ctor_set(v___x_764_, 1, v___x_745_);
lean_ctor_set(v___x_764_, 2, v___x_746_);
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = lean_substring_drop(v___x_764_, v___x_765_);
v___x_767_ = lean_substring_all(v___x_766_, v___f_762_);
v___y_760_ = v___x_767_;
goto v___jp_759_;
}
v___jp_768_:
{
if (v___y_769_ == 0)
{
goto v___jp_753_;
}
else
{
goto v___jp_763_;
}
}
v___jp_770_:
{
if (v___y_772_ == 0)
{
uint32_t v___x_773_; uint8_t v___x_774_; 
v___x_773_ = 95;
v___x_774_ = lean_uint32_dec_eq(v___y_771_, v___x_773_);
if (v___x_774_ == 0)
{
uint8_t v___x_775_; 
v___x_775_ = l_Lean_isLetterLike(v___y_771_);
v___y_769_ = v___x_775_;
goto v___jp_768_;
}
else
{
v___y_769_ = v___x_774_;
goto v___jp_768_;
}
}
else
{
goto v___jp_763_;
}
}
v___jp_776_:
{
uint32_t v___x_778_; uint8_t v___x_779_; 
v___x_778_ = 97;
v___x_779_ = lean_uint32_dec_le(v___x_778_, v___y_777_);
if (v___x_779_ == 0)
{
v___y_771_ = v___y_777_;
v___y_772_ = v___x_779_;
goto v___jp_770_;
}
else
{
uint32_t v___x_780_; uint8_t v___x_781_; 
v___x_780_ = 122;
v___x_781_ = lean_uint32_dec_le(v___y_777_, v___x_780_);
v___y_771_ = v___y_777_;
v___y_772_ = v___x_781_;
goto v___jp_770_;
}
}
v___jp_782_:
{
if (v___y_783_ == 0)
{
uint32_t v___x_784_; uint32_t v___x_785_; uint8_t v___x_786_; 
v___x_784_ = lean_string_utf8_get(v_s_743_, v___x_745_);
v___x_785_ = 65;
v___x_786_ = lean_uint32_dec_le(v___x_785_, v___x_784_);
if (v___x_786_ == 0)
{
v___y_777_ = v___x_784_;
goto v___jp_776_;
}
else
{
uint32_t v___x_787_; uint8_t v___x_788_; 
v___x_787_ = 90;
v___x_788_ = lean_uint32_dec_le(v___x_784_, v___x_787_);
if (v___x_788_ == 0)
{
v___y_777_ = v___x_784_;
goto v___jp_776_;
}
else
{
goto v___jp_763_;
}
}
}
else
{
return v_s_743_;
}
}
v___jp_789_:
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_743_, v___x_790_);
v___y_783_ = v___x_791_;
goto v___jp_782_;
}
v___jp_793_:
{
if (v___y_794_ == 0)
{
uint8_t v___x_795_; uint8_t v___x_796_; 
v___x_795_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_796_ = lean_uint8_dec_eq(v_c_792_, v___x_795_);
if (v___x_796_ == 0)
{
v___y_783_ = v___x_796_;
goto v___jp_782_;
}
else
{
goto v___jp_789_;
}
}
else
{
goto v___jp_789_;
}
}
v___jp_797_:
{
if (v___y_798_ == 0)
{
uint8_t v___x_799_; uint8_t v___x_800_; 
v___x_799_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_800_ = lean_uint8_dec_le(v___x_799_, v_c_792_);
if (v___x_800_ == 0)
{
v___y_794_ = v___x_800_;
goto v___jp_793_;
}
else
{
uint8_t v___x_801_; uint8_t v___x_802_; 
v___x_801_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_802_ = lean_uint8_dec_le(v_c_792_, v___x_801_);
v___y_794_ = v___x_802_;
goto v___jp_793_;
}
}
else
{
goto v___jp_789_;
}
}
}
v___jp_753_:
{
uint8_t v___x_754_; 
lean_inc_ref(v_s_743_);
v___x_754_ = lean_string_any(v_s_743_, v___f_752_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_755_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_756_ = lean_string_append(v___x_755_, v_s_743_);
lean_dec_ref(v_s_743_);
v___x_757_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_758_ = lean_string_append(v___x_756_, v___x_757_);
return v___x_758_;
}
else
{
return v_s_743_;
}
}
v___jp_759_:
{
if (v___y_760_ == 0)
{
goto v___jp_753_;
}
else
{
return v_s_743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_807_, lean_object* v_s_808_, lean_object* v_force_809_){
_start:
{
uint8_t v_escape_boxed_810_; uint8_t v_force_boxed_811_; lean_object* v_res_812_; 
v_escape_boxed_810_ = lean_unbox(v_escape_807_);
v_force_boxed_811_ = lean_unbox(v_force_809_);
v_res_812_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_boxed_810_, v_s_808_, v_force_boxed_811_);
return v_res_812_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object* v_x_813_){
_start:
{
uint8_t v___x_814_; 
v___x_814_ = 0;
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed(lean_object* v_x_815_){
_start:
{
uint8_t v_res_816_; lean_object* v_r_817_; 
v_res_816_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(v_x_815_);
lean_dec_ref(v_x_815_);
v_r_817_ = lean_box(v_res_816_);
return v_r_817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object* v_sep_820_, uint8_t v_escape_821_, lean_object* v_n_822_, lean_object* v_isToken_823_){
_start:
{
switch(lean_obj_tag(v_n_822_))
{
case 0:
{
lean_object* v___x_824_; 
lean_dec_ref(v_isToken_823_);
v___x_824_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_824_;
}
case 1:
{
lean_object* v_pre_825_; 
v_pre_825_ = lean_ctor_get(v_n_822_, 0);
if (lean_obj_tag(v_pre_825_) == 0)
{
lean_object* v_str_826_; lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v___x_829_; 
v_str_826_ = lean_ctor_get(v_n_822_, 1);
lean_inc_ref_n(v_str_826_, 2);
lean_dec_ref_known(v_n_822_, 2);
v___x_827_ = lean_apply_1(v_isToken_823_, v_str_826_);
v___x_828_ = lean_unbox(v___x_827_);
v___x_829_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_821_, v_str_826_, v___x_828_);
return v___x_829_;
}
else
{
lean_object* v_str_830_; lean_object* v_r_831_; lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v_r_x27_835_; 
lean_inc(v_pre_825_);
v_str_830_ = lean_ctor_get(v_n_822_, 1);
lean_inc_ref_n(v_str_830_, 2);
lean_dec_ref_known(v_n_822_, 2);
lean_inc_ref(v_isToken_823_);
v_r_831_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_820_, v_escape_821_, v_pre_825_, v_isToken_823_);
v___x_832_ = lean_string_append(v_r_831_, v_sep_820_);
v___x_833_ = 0;
v___x_834_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_821_, v_str_830_, v___x_833_);
lean_inc_ref(v___x_832_);
v_r_x27_835_ = lean_string_append(v___x_832_, v___x_834_);
lean_dec_ref(v___x_834_);
if (v_escape_821_ == 0)
{
lean_dec_ref(v___x_832_);
lean_dec_ref(v_str_830_);
lean_dec_ref(v_isToken_823_);
return v_r_x27_835_;
}
else
{
lean_object* v___x_836_; uint8_t v___x_837_; 
lean_inc_ref(v_r_x27_835_);
v___x_836_ = lean_apply_1(v_isToken_823_, v_r_x27_835_);
v___x_837_ = lean_unbox(v___x_836_);
if (v___x_837_ == 0)
{
lean_dec_ref(v___x_832_);
lean_dec_ref(v_str_830_);
return v_r_x27_835_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec_ref(v_r_x27_835_);
v___x_838_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_821_, v_str_830_, v_escape_821_);
v___x_839_ = lean_string_append(v___x_832_, v___x_838_);
lean_dec_ref(v___x_838_);
return v___x_839_;
}
}
}
}
default: 
{
lean_object* v_pre_840_; 
lean_dec_ref(v_isToken_823_);
v_pre_840_ = lean_ctor_get(v_n_822_, 0);
if (lean_obj_tag(v_pre_840_) == 0)
{
lean_object* v_i_841_; lean_object* v___x_842_; 
v_i_841_ = lean_ctor_get(v_n_822_, 1);
lean_inc(v_i_841_);
lean_dec_ref_known(v_n_822_, 2);
v___x_842_ = l_Nat_reprFast(v_i_841_);
return v___x_842_;
}
else
{
lean_object* v_i_843_; lean_object* v___f_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
lean_inc(v_pre_840_);
v_i_843_ = lean_ctor_get(v_n_822_, 1);
lean_inc(v_i_843_);
lean_dec_ref_known(v_n_822_, 2);
v___f_844_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1));
v___x_845_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_820_, v_escape_821_, v_pre_840_, v___f_844_);
v___x_846_ = lean_string_append(v___x_845_, v_sep_820_);
v___x_847_ = l_Nat_reprFast(v_i_843_);
v___x_848_ = lean_string_append(v___x_846_, v___x_847_);
lean_dec_ref(v___x_847_);
return v___x_848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object* v_sep_849_, lean_object* v_escape_850_, lean_object* v_n_851_, lean_object* v_isToken_852_){
_start:
{
uint8_t v_escape_boxed_853_; lean_object* v_res_854_; 
v_escape_boxed_853_ = lean_unbox(v_escape_850_);
v_res_854_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_849_, v_escape_boxed_853_, v_n_851_, v_isToken_852_);
lean_dec_ref(v_sep_849_);
return v_res_854_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object* v_n_860_){
_start:
{
lean_object* v___x_861_; uint8_t v___x_862_; uint8_t v___x_863_; 
v___x_861_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_862_ = lean_name_eq(v_n_860_, v___x_861_);
v___x_863_ = 1;
if (v___x_862_ == 0)
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Name_getRoot(v_n_860_);
if (lean_obj_tag(v___x_864_) == 1)
{
lean_object* v_str_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v_str_865_ = lean_ctor_get(v___x_864_, 1);
lean_inc_ref_n(v_str_865_, 2);
lean_dec_ref_known(v___x_864_, 2);
v___x_866_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_867_ = lean_string_isprefixof(v___x_866_, v_str_865_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_868_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3));
v___x_869_ = lean_string_isprefixof(v___x_868_, v_str_865_);
return v___x_869_;
}
else
{
lean_dec_ref(v_str_865_);
return v___x_863_;
}
}
else
{
lean_dec(v___x_864_);
return v___x_862_;
}
}
else
{
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_870_){
_start:
{
uint8_t v_res_871_; lean_object* v_r_872_; 
v_res_871_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_870_);
lean_dec(v_n_870_);
v_r_872_ = lean_box(v_res_871_);
return v_r_872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object* v_n_873_, uint8_t v_escape_874_, lean_object* v_isToken_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_874_ == 0)
{
lean_object* v___x_877_; 
v___x_877_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_876_, v_escape_874_, v_n_873_, v_isToken_875_);
return v___x_877_;
}
else
{
uint8_t v___x_878_; uint8_t v___x_879_; 
lean_inc(v_n_873_);
v___x_878_ = l_Lean_Name_isInaccessibleUserName(v_n_873_);
v___x_879_ = lean_bool_not(v___x_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; 
v___x_880_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_876_, v___x_879_, v_n_873_, v_isToken_875_);
return v___x_880_;
}
else
{
uint8_t v___x_881_; uint8_t v___x_882_; 
v___x_881_ = l_Lean_Name_hasMacroScopes(v_n_873_);
v___x_882_ = lean_bool_not(v___x_881_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; 
v___x_883_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_876_, v___x_882_, v_n_873_, v_isToken_875_);
return v___x_883_;
}
else
{
uint8_t v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; 
v___x_884_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_873_);
v___x_885_ = lean_bool_not(v___x_884_);
v___x_886_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_876_, v___x_885_, v_n_873_, v_isToken_875_);
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object* v_n_887_, lean_object* v_escape_888_, lean_object* v_isToken_889_){
_start:
{
uint8_t v_escape_boxed_890_; lean_object* v_res_891_; 
v_escape_boxed_890_ = lean_unbox(v_escape_888_);
v_res_891_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(v_n_887_, v_escape_boxed_890_, v_isToken_889_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object* v_sep_892_, uint8_t v_escape_893_, lean_object* v_n_894_){
_start:
{
switch(lean_obj_tag(v_n_894_))
{
case 0:
{
lean_object* v___x_895_; 
v___x_895_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_895_;
}
case 1:
{
lean_object* v_pre_896_; 
v_pre_896_ = lean_ctor_get(v_n_894_, 0);
if (lean_obj_tag(v_pre_896_) == 0)
{
lean_object* v_str_897_; uint8_t v___x_898_; lean_object* v___x_899_; 
v_str_897_ = lean_ctor_get(v_n_894_, 1);
lean_inc_ref(v_str_897_);
lean_dec_ref_known(v_n_894_, 2);
v___x_898_ = 0;
v___x_899_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_893_, v_str_897_, v___x_898_);
return v___x_899_;
}
else
{
lean_object* v_str_900_; lean_object* v_r_901_; lean_object* v___x_902_; uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v_r_x27_905_; 
lean_inc(v_pre_896_);
v_str_900_ = lean_ctor_get(v_n_894_, 1);
lean_inc_ref(v_str_900_);
lean_dec_ref_known(v_n_894_, 2);
v_r_901_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_892_, v_escape_893_, v_pre_896_);
v___x_902_ = lean_string_append(v_r_901_, v_sep_892_);
v___x_903_ = 0;
v___x_904_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_893_, v_str_900_, v___x_903_);
v_r_x27_905_ = lean_string_append(v___x_902_, v___x_904_);
lean_dec_ref(v___x_904_);
return v_r_x27_905_;
}
}
default: 
{
lean_object* v_pre_906_; 
v_pre_906_ = lean_ctor_get(v_n_894_, 0);
if (lean_obj_tag(v_pre_906_) == 0)
{
lean_object* v_i_907_; lean_object* v___x_908_; 
v_i_907_ = lean_ctor_get(v_n_894_, 1);
lean_inc(v_i_907_);
lean_dec_ref_known(v_n_894_, 2);
v___x_908_ = l_Nat_reprFast(v_i_907_);
return v___x_908_;
}
else
{
lean_object* v_i_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_inc(v_pre_906_);
v_i_909_ = lean_ctor_get(v_n_894_, 1);
lean_inc(v_i_909_);
lean_dec_ref_known(v_n_894_, 2);
v___x_910_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_892_, v_escape_893_, v_pre_906_);
v___x_911_ = lean_string_append(v___x_910_, v_sep_892_);
v___x_912_ = l_Nat_reprFast(v_i_909_);
v___x_913_ = lean_string_append(v___x_911_, v___x_912_);
lean_dec_ref(v___x_912_);
return v___x_913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object* v_sep_914_, lean_object* v_escape_915_, lean_object* v_n_916_){
_start:
{
uint8_t v_escape_boxed_917_; lean_object* v_res_918_; 
v_escape_boxed_917_ = lean_unbox(v_escape_915_);
v_res_918_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_914_, v_escape_boxed_917_, v_n_916_);
lean_dec_ref(v_sep_914_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object* v_n_919_, uint8_t v_escape_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_920_ == 0)
{
lean_object* v___x_922_; 
v___x_922_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_921_, v_escape_920_, v_n_919_);
return v___x_922_;
}
else
{
uint8_t v___x_923_; uint8_t v___x_924_; 
lean_inc(v_n_919_);
v___x_923_ = l_Lean_Name_isInaccessibleUserName(v_n_919_);
v___x_924_ = lean_bool_not(v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; 
v___x_925_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_921_, v___x_924_, v_n_919_);
return v___x_925_;
}
else
{
uint8_t v___x_926_; uint8_t v___x_927_; 
v___x_926_ = l_Lean_Name_hasMacroScopes(v_n_919_);
v___x_927_ = lean_bool_not(v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; 
v___x_928_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_921_, v___x_927_, v_n_919_);
return v___x_928_;
}
else
{
uint8_t v___x_929_; uint8_t v___x_930_; lean_object* v___x_931_; 
v___x_929_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_919_);
v___x_930_ = lean_bool_not(v___x_929_);
v___x_931_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_921_, v___x_930_, v_n_919_);
return v___x_931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object* v_n_932_, lean_object* v_escape_933_){
_start:
{
uint8_t v_escape_boxed_934_; lean_object* v_res_935_; 
v_escape_boxed_934_ = lean_unbox(v_escape_933_);
v_res_935_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_932_, v_escape_boxed_934_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object* v_n_936_, uint8_t v_escape_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_936_, v_escape_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object* v_n_939_, lean_object* v_escape_940_){
_start:
{
uint8_t v_escape_boxed_941_; lean_object* v_res_942_; 
v_escape_boxed_941_ = lean_unbox(v_escape_940_);
v_res_942_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(v_n_939_, v_escape_boxed_941_);
return v_res_942_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_hasNum(lean_object* v_x_943_){
_start:
{
switch(lean_obj_tag(v_x_943_))
{
case 0:
{
uint8_t v___x_944_; 
v___x_944_ = 0;
return v___x_944_;
}
case 1:
{
lean_object* v_pre_945_; 
v_pre_945_ = lean_ctor_get(v_x_943_, 0);
v_x_943_ = v_pre_945_;
goto _start;
}
default: 
{
uint8_t v___x_947_; 
v___x_947_ = 1;
return v___x_947_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_hasNum___boxed(lean_object* v_x_948_){
_start:
{
uint8_t v_res_949_; lean_object* v_r_950_; 
v_res_949_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_x_948_);
lean_dec(v_x_948_);
v_r_950_ = lean_box(v_res_949_);
return v_r_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object* v_n_966_, lean_object* v_prec_967_){
_start:
{
switch(lean_obj_tag(v_n_966_))
{
case 0:
{
lean_object* v___x_968_; 
v___x_968_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__1));
return v___x_968_;
}
case 1:
{
lean_object* v_pre_969_; lean_object* v_str_970_; uint8_t v___x_971_; 
v_pre_969_ = lean_ctor_get(v_n_966_, 0);
v_str_970_ = lean_ctor_get(v_n_966_, 1);
v___x_971_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_pre_969_);
if (v___x_971_ == 0)
{
uint8_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_972_ = 1;
v___x_973_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__3));
v___x_974_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_966_, v___x_972_);
v___x_975_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_973_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
return v___x_976_;
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
lean_inc_ref(v_str_970_);
lean_inc(v_pre_969_);
lean_dec_ref_known(v_n_966_, 2);
v___x_977_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__5));
v___x_978_ = lean_unsigned_to_nat(1024u);
v___x_979_ = l_Lean_Name_reprPrec(v_pre_969_, v___x_978_);
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_977_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = l_String_quote(v_str_970_);
v___x_984_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_982_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = l_Repr_addAppParen(v___x_985_, v_prec_967_);
return v___x_986_;
}
}
default: 
{
lean_object* v_pre_987_; lean_object* v_i_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_pre_987_ = lean_ctor_get(v_n_966_, 0);
lean_inc(v_pre_987_);
v_i_988_ = lean_ctor_get(v_n_966_, 1);
lean_inc(v_i_988_);
lean_dec_ref_known(v_n_966_, 2);
v___x_989_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__9));
v___x_990_ = lean_unsigned_to_nat(1024u);
v___x_991_ = l_Lean_Name_reprPrec(v_pre_987_, v___x_990_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_989_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = l_Nat_reprFast(v_i_988_);
v___x_996_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_994_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l_Repr_addAppParen(v___x_997_, v_prec_967_);
return v___x_998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object* v_n_999_, lean_object* v_prec_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Name_reprPrec(v_n_999_, v_prec_1000_);
lean_dec(v_prec_1000_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object* v_x_1004_){
_start:
{
if (lean_obj_tag(v_x_1004_) == 1)
{
lean_object* v_pre_1005_; lean_object* v_str_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_pre_1005_ = lean_ctor_get(v_x_1004_, 0);
lean_inc(v_pre_1005_);
v_str_1006_ = lean_ctor_get(v_x_1004_, 1);
lean_inc_ref(v_str_1006_);
lean_dec_ref_known(v_x_1004_, 2);
v___x_1007_ = lean_string_capitalize(v_str_1006_);
v___x_1008_ = l_Lean_Name_str___override(v_pre_1005_, v___x_1007_);
return v___x_1008_;
}
else
{
return v_x_1004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
switch(lean_obj_tag(v_x_1009_))
{
case 0:
{
if (lean_obj_tag(v_x_1010_) == 0)
{
lean_inc(v_x_1011_);
return v_x_1011_;
}
else
{
return v_x_1009_;
}
}
case 1:
{
lean_object* v_pre_1012_; lean_object* v_str_1013_; uint8_t v___x_1014_; 
v_pre_1012_ = lean_ctor_get(v_x_1009_, 0);
lean_inc(v_pre_1012_);
v_str_1013_ = lean_ctor_get(v_x_1009_, 1);
lean_inc_ref(v_str_1013_);
v___x_1014_ = lean_name_eq(v_x_1009_, v_x_1010_);
lean_dec_ref_known(v_x_1009_, 2);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = l_Lean_Name_replacePrefix(v_pre_1012_, v_x_1010_, v_x_1011_);
v___x_1016_ = l_Lean_Name_str___override(v___x_1015_, v_str_1013_);
return v___x_1016_;
}
else
{
lean_dec_ref(v_str_1013_);
lean_dec(v_pre_1012_);
lean_inc(v_x_1011_);
return v_x_1011_;
}
}
default: 
{
lean_object* v_pre_1017_; lean_object* v_i_1018_; uint8_t v___x_1019_; 
v_pre_1017_ = lean_ctor_get(v_x_1009_, 0);
lean_inc(v_pre_1017_);
v_i_1018_ = lean_ctor_get(v_x_1009_, 1);
lean_inc(v_i_1018_);
v___x_1019_ = lean_name_eq(v_x_1009_, v_x_1010_);
lean_dec_ref_known(v_x_1009_, 2);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = l_Lean_Name_replacePrefix(v_pre_1017_, v_x_1010_, v_x_1011_);
v___x_1021_ = l_Lean_Name_num___override(v___x_1020_, v_i_1018_);
return v___x_1021_;
}
else
{
lean_dec(v_i_1018_);
lean_dec(v_pre_1017_);
lean_inc(v_x_1011_);
return v_x_1011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object* v_x_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Name_replacePrefix(v_x_1022_, v_x_1023_, v_x_1024_);
lean_dec(v_x_1024_);
lean_dec(v_x_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object* v_x_1026_, lean_object* v_x_1027_){
_start:
{
switch(lean_obj_tag(v_x_1027_))
{
case 0:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1028_, 0, v_x_1026_);
return v___x_1028_;
}
case 1:
{
if (lean_obj_tag(v_x_1026_) == 1)
{
lean_object* v_pre_1029_; lean_object* v_str_1030_; lean_object* v_pre_1031_; lean_object* v_str_1032_; uint8_t v___x_1033_; 
v_pre_1029_ = lean_ctor_get(v_x_1027_, 0);
v_str_1030_ = lean_ctor_get(v_x_1027_, 1);
v_pre_1031_ = lean_ctor_get(v_x_1026_, 0);
lean_inc(v_pre_1031_);
v_str_1032_ = lean_ctor_get(v_x_1026_, 1);
lean_inc_ref(v_str_1032_);
lean_dec_ref_known(v_x_1026_, 2);
v___x_1033_ = lean_string_dec_eq(v_str_1032_, v_str_1030_);
lean_dec_ref(v_str_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; 
lean_dec(v_pre_1031_);
v___x_1034_ = lean_box(0);
return v___x_1034_;
}
else
{
v_x_1026_ = v_pre_1031_;
v_x_1027_ = v_pre_1029_;
goto _start;
}
}
else
{
lean_object* v___x_1036_; 
lean_dec(v_x_1026_);
v___x_1036_ = lean_box(0);
return v___x_1036_;
}
}
default: 
{
if (lean_obj_tag(v_x_1026_) == 2)
{
lean_object* v_pre_1037_; lean_object* v_i_1038_; lean_object* v_pre_1039_; lean_object* v_i_1040_; uint8_t v___x_1041_; 
v_pre_1037_ = lean_ctor_get(v_x_1027_, 0);
v_i_1038_ = lean_ctor_get(v_x_1027_, 1);
v_pre_1039_ = lean_ctor_get(v_x_1026_, 0);
lean_inc(v_pre_1039_);
v_i_1040_ = lean_ctor_get(v_x_1026_, 1);
lean_inc(v_i_1040_);
lean_dec_ref_known(v_x_1026_, 2);
v___x_1041_ = lean_nat_dec_eq(v_i_1040_, v_i_1038_);
lean_dec(v_i_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; 
lean_dec(v_pre_1039_);
v___x_1042_ = lean_box(0);
return v___x_1042_;
}
else
{
v_x_1026_ = v_pre_1039_;
v_x_1027_ = v_pre_1037_;
goto _start;
}
}
else
{
lean_object* v___x_1044_; 
lean_dec(v_x_1026_);
v___x_1044_ = lean_box(0);
return v___x_1044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_Name_eraseSuffix_x3f(v_x_1045_, v_x_1046_);
lean_dec(v_x_1046_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object* v_n_1048_, lean_object* v_f_1049_){
_start:
{
uint8_t v___x_1050_; 
v___x_1050_ = l_Lean_Name_hasMacroScopes(v_n_1048_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_apply_1(v_f_1049_, v_n_1048_);
return v___x_1051_;
}
else
{
lean_object* v_view_1052_; lean_object* v_name_1053_; lean_object* v_imported_1054_; lean_object* v_ctx_1055_; lean_object* v_scopes_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1065_; 
v_view_1052_ = l_Lean_extractMacroScopes(v_n_1048_);
v_name_1053_ = lean_ctor_get(v_view_1052_, 0);
v_imported_1054_ = lean_ctor_get(v_view_1052_, 1);
v_ctx_1055_ = lean_ctor_get(v_view_1052_, 2);
v_scopes_1056_ = lean_ctor_get(v_view_1052_, 3);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_view_1052_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1058_ = v_view_1052_;
v_isShared_1059_ = v_isSharedCheck_1065_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_scopes_1056_);
lean_inc(v_ctx_1055_);
lean_inc(v_imported_1054_);
lean_inc(v_name_1053_);
lean_dec(v_view_1052_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1065_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1060_ = lean_apply_1(v_f_1049_, v_name_1053_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1060_);
v___x_1062_ = v___x_1058_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_imported_1054_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_ctx_1055_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_scopes_1056_);
v___x_1062_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_MacroScopesView_review(v___x_1062_);
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object* v_suffix_1066_, lean_object* v_x_1067_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 1)
{
lean_object* v_pre_1068_; lean_object* v_str_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_pre_1068_ = lean_ctor_get(v_x_1067_, 0);
lean_inc(v_pre_1068_);
v_str_1069_ = lean_ctor_get(v_x_1067_, 1);
lean_inc_ref(v_str_1069_);
lean_dec_ref_known(v_x_1067_, 2);
v___x_1070_ = lean_string_append(v_str_1069_, v_suffix_1066_);
lean_dec_ref(v_suffix_1066_);
v___x_1071_ = l_Lean_Name_str___override(v_pre_1068_, v___x_1070_);
return v___x_1071_;
}
else
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Name_str___override(v_x_1067_, v_suffix_1066_);
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_after(lean_object* v_n_1073_, lean_object* v_suffix_1074_){
_start:
{
uint8_t v___x_1075_; 
v___x_1075_ = l_Lean_Name_hasMacroScopes(v_n_1073_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_Name_appendAfter___lam__0(v_suffix_1074_, v_n_1073_);
return v___x_1076_;
}
else
{
lean_object* v_view_1077_; lean_object* v_name_1078_; lean_object* v_imported_1079_; lean_object* v_ctx_1080_; lean_object* v_scopes_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1090_; 
v_view_1077_ = l_Lean_extractMacroScopes(v_n_1073_);
v_name_1078_ = lean_ctor_get(v_view_1077_, 0);
v_imported_1079_ = lean_ctor_get(v_view_1077_, 1);
v_ctx_1080_ = lean_ctor_get(v_view_1077_, 2);
v_scopes_1081_ = lean_ctor_get(v_view_1077_, 3);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_view_1077_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1083_ = v_view_1077_;
v_isShared_1084_ = v_isSharedCheck_1090_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_scopes_1081_);
lean_inc(v_ctx_1080_);
lean_inc(v_imported_1079_);
lean_inc(v_name_1078_);
lean_dec(v_view_1077_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1090_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = l_Lean_Name_appendAfter___lam__0(v_suffix_1074_, v_name_1078_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1085_);
v___x_1087_ = v___x_1083_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_imported_1079_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_ctx_1080_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_scopes_1081_);
v___x_1087_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_MacroScopesView_review(v___x_1087_);
return v___x_1088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object* v_idx_1091_, lean_object* v_x_1092_){
_start:
{
if (lean_obj_tag(v_x_1092_) == 1)
{
lean_object* v_pre_1093_; lean_object* v_str_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_pre_1093_ = lean_ctor_get(v_x_1092_, 0);
lean_inc(v_pre_1093_);
v_str_1094_ = lean_ctor_get(v_x_1092_, 1);
lean_inc_ref(v_str_1094_);
lean_dec_ref_known(v_x_1092_, 2);
v___x_1095_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1096_ = lean_string_append(v_str_1094_, v___x_1095_);
v___x_1097_ = l_Nat_reprFast(v_idx_1091_);
v___x_1098_ = lean_string_append(v___x_1096_, v___x_1097_);
lean_dec_ref(v___x_1097_);
v___x_1099_ = l_Lean_Name_str___override(v_pre_1093_, v___x_1098_);
return v___x_1099_;
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1100_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1101_ = l_Nat_reprFast(v_idx_1091_);
v___x_1102_ = lean_string_append(v___x_1100_, v___x_1101_);
lean_dec_ref(v___x_1101_);
v___x_1103_ = l_Lean_Name_str___override(v_x_1092_, v___x_1102_);
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object* v_n_1104_, lean_object* v_idx_1105_){
_start:
{
uint8_t v___x_1106_; 
v___x_1106_ = l_Lean_Name_hasMacroScopes(v_n_1104_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1105_, v_n_1104_);
return v___x_1107_;
}
else
{
lean_object* v_view_1108_; lean_object* v_name_1109_; lean_object* v_imported_1110_; lean_object* v_ctx_1111_; lean_object* v_scopes_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1121_; 
v_view_1108_ = l_Lean_extractMacroScopes(v_n_1104_);
v_name_1109_ = lean_ctor_get(v_view_1108_, 0);
v_imported_1110_ = lean_ctor_get(v_view_1108_, 1);
v_ctx_1111_ = lean_ctor_get(v_view_1108_, 2);
v_scopes_1112_ = lean_ctor_get(v_view_1108_, 3);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_view_1108_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1114_ = v_view_1108_;
v_isShared_1115_ = v_isSharedCheck_1121_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_scopes_1112_);
lean_inc(v_ctx_1111_);
lean_inc(v_imported_1110_);
lean_inc(v_name_1109_);
lean_dec(v_view_1108_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1121_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1116_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1105_, v_name_1109_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1116_);
v___x_1118_ = v___x_1114_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_imported_1110_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_ctx_1111_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_scopes_1112_);
v___x_1118_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_MacroScopesView_review(v___x_1118_);
return v___x_1119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object* v_pre_1122_, lean_object* v_x_1123_){
_start:
{
switch(lean_obj_tag(v_x_1123_))
{
case 0:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_Name_str___override(v_x_1123_, v_pre_1122_);
return v___x_1124_;
}
case 1:
{
lean_object* v_pre_1125_; lean_object* v_str_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_pre_1125_ = lean_ctor_get(v_x_1123_, 0);
lean_inc(v_pre_1125_);
v_str_1126_ = lean_ctor_get(v_x_1123_, 1);
lean_inc_ref(v_str_1126_);
lean_dec_ref_known(v_x_1123_, 2);
v___x_1127_ = lean_string_append(v_pre_1122_, v_str_1126_);
lean_dec_ref(v_str_1126_);
v___x_1128_ = l_Lean_Name_str___override(v_pre_1125_, v___x_1127_);
return v___x_1128_;
}
default: 
{
lean_object* v_pre_1129_; lean_object* v_i_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_pre_1129_ = lean_ctor_get(v_x_1123_, 0);
lean_inc(v_pre_1129_);
v_i_1130_ = lean_ctor_get(v_x_1123_, 1);
lean_inc(v_i_1130_);
lean_dec_ref_known(v_x_1123_, 2);
v___x_1131_ = l_Lean_Name_str___override(v_pre_1129_, v_pre_1122_);
v___x_1132_ = l_Lean_Name_num___override(v___x_1131_, v_i_1130_);
return v___x_1132_;
}
}
}
}
LEAN_EXPORT lean_object* lean_name_append_before(lean_object* v_n_1133_, lean_object* v_pre_1134_){
_start:
{
uint8_t v___x_1135_; 
v___x_1135_ = l_Lean_Name_hasMacroScopes(v_n_1133_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_Name_appendBefore___lam__0(v_pre_1134_, v_n_1133_);
return v___x_1136_;
}
else
{
lean_object* v_view_1137_; lean_object* v_name_1138_; lean_object* v_imported_1139_; lean_object* v_ctx_1140_; lean_object* v_scopes_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1150_; 
v_view_1137_ = l_Lean_extractMacroScopes(v_n_1133_);
v_name_1138_ = lean_ctor_get(v_view_1137_, 0);
v_imported_1139_ = lean_ctor_get(v_view_1137_, 1);
v_ctx_1140_ = lean_ctor_get(v_view_1137_, 2);
v_scopes_1141_ = lean_ctor_get(v_view_1137_, 3);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_view_1137_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1143_ = v_view_1137_;
v_isShared_1144_ = v_isSharedCheck_1150_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_scopes_1141_);
lean_inc(v_ctx_1140_);
lean_inc(v_imported_1139_);
lean_inc(v_name_1138_);
lean_dec(v_view_1137_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1150_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = l_Lean_Name_appendBefore___lam__0(v_pre_1134_, v_name_1138_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1145_);
v___x_1147_ = v___x_1143_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_imported_1139_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_ctx_1140_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_scopes_1141_);
v___x_1147_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_MacroScopesView_review(v___x_1147_);
return v___x_1148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object* v_x_1151_, lean_object* v_x_1152_, lean_object* v_h__1_1153_, lean_object* v_h__2_1154_, lean_object* v_h__3_1155_, lean_object* v_h__4_1156_){
_start:
{
switch(lean_obj_tag(v_x_1151_))
{
case 0:
{
lean_dec(v_h__3_1155_);
lean_dec(v_h__2_1154_);
if (lean_obj_tag(v_x_1152_) == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v_h__4_1156_);
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_apply_1(v_h__1_1153_, v___x_1157_);
return v___x_1158_;
}
else
{
lean_object* v___x_1159_; 
lean_dec(v_h__1_1153_);
v___x_1159_ = lean_apply_5(v_h__4_1156_, v_x_1151_, v_x_1152_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1159_;
}
}
case 1:
{
lean_dec(v_h__3_1155_);
lean_dec(v_h__1_1153_);
if (lean_obj_tag(v_x_1152_) == 1)
{
lean_object* v_pre_1160_; lean_object* v_str_1161_; lean_object* v_pre_1162_; lean_object* v_str_1163_; lean_object* v___x_1164_; 
lean_dec(v_h__4_1156_);
v_pre_1160_ = lean_ctor_get(v_x_1151_, 0);
lean_inc(v_pre_1160_);
v_str_1161_ = lean_ctor_get(v_x_1151_, 1);
lean_inc_ref(v_str_1161_);
lean_dec_ref_known(v_x_1151_, 2);
v_pre_1162_ = lean_ctor_get(v_x_1152_, 0);
lean_inc(v_pre_1162_);
v_str_1163_ = lean_ctor_get(v_x_1152_, 1);
lean_inc_ref(v_str_1163_);
lean_dec_ref_known(v_x_1152_, 2);
v___x_1164_ = lean_apply_4(v_h__2_1154_, v_pre_1160_, v_str_1161_, v_pre_1162_, v_str_1163_);
return v___x_1164_;
}
else
{
lean_object* v___x_1165_; 
lean_dec(v_h__2_1154_);
v___x_1165_ = lean_apply_5(v_h__4_1156_, v_x_1151_, v_x_1152_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1165_;
}
}
default: 
{
lean_dec(v_h__2_1154_);
lean_dec(v_h__1_1153_);
if (lean_obj_tag(v_x_1152_) == 2)
{
lean_object* v_pre_1166_; lean_object* v_i_1167_; lean_object* v_pre_1168_; lean_object* v_i_1169_; lean_object* v___x_1170_; 
lean_dec(v_h__4_1156_);
v_pre_1166_ = lean_ctor_get(v_x_1151_, 0);
lean_inc(v_pre_1166_);
v_i_1167_ = lean_ctor_get(v_x_1151_, 1);
lean_inc(v_i_1167_);
lean_dec_ref_known(v_x_1151_, 2);
v_pre_1168_ = lean_ctor_get(v_x_1152_, 0);
lean_inc(v_pre_1168_);
v_i_1169_ = lean_ctor_get(v_x_1152_, 1);
lean_inc(v_i_1169_);
lean_dec_ref_known(v_x_1152_, 2);
v___x_1170_ = lean_apply_4(v_h__3_1155_, v_pre_1166_, v_i_1167_, v_pre_1168_, v_i_1169_);
return v___x_1170_;
}
else
{
lean_object* v___x_1171_; 
lean_dec(v_h__3_1155_);
v___x_1171_ = lean_apply_5(v_h__4_1156_, v_x_1151_, v_x_1152_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object* v_motive_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_, lean_object* v_h__1_1175_, lean_object* v_h__2_1176_, lean_object* v_h__3_1177_, lean_object* v_h__4_1178_){
_start:
{
switch(lean_obj_tag(v_x_1173_))
{
case 0:
{
lean_dec(v_h__3_1177_);
lean_dec(v_h__2_1176_);
if (lean_obj_tag(v_x_1174_) == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec(v_h__4_1178_);
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_apply_1(v_h__1_1175_, v___x_1179_);
return v___x_1180_;
}
else
{
lean_object* v___x_1181_; 
lean_dec(v_h__1_1175_);
v___x_1181_ = lean_apply_5(v_h__4_1178_, v_x_1173_, v_x_1174_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1181_;
}
}
case 1:
{
lean_dec(v_h__3_1177_);
lean_dec(v_h__1_1175_);
if (lean_obj_tag(v_x_1174_) == 1)
{
lean_object* v_pre_1182_; lean_object* v_str_1183_; lean_object* v_pre_1184_; lean_object* v_str_1185_; lean_object* v___x_1186_; 
lean_dec(v_h__4_1178_);
v_pre_1182_ = lean_ctor_get(v_x_1173_, 0);
lean_inc(v_pre_1182_);
v_str_1183_ = lean_ctor_get(v_x_1173_, 1);
lean_inc_ref(v_str_1183_);
lean_dec_ref_known(v_x_1173_, 2);
v_pre_1184_ = lean_ctor_get(v_x_1174_, 0);
lean_inc(v_pre_1184_);
v_str_1185_ = lean_ctor_get(v_x_1174_, 1);
lean_inc_ref(v_str_1185_);
lean_dec_ref_known(v_x_1174_, 2);
v___x_1186_ = lean_apply_4(v_h__2_1176_, v_pre_1182_, v_str_1183_, v_pre_1184_, v_str_1185_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; 
lean_dec(v_h__2_1176_);
v___x_1187_ = lean_apply_5(v_h__4_1178_, v_x_1173_, v_x_1174_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1187_;
}
}
default: 
{
lean_dec(v_h__2_1176_);
lean_dec(v_h__1_1175_);
if (lean_obj_tag(v_x_1174_) == 2)
{
lean_object* v_pre_1188_; lean_object* v_i_1189_; lean_object* v_pre_1190_; lean_object* v_i_1191_; lean_object* v___x_1192_; 
lean_dec(v_h__4_1178_);
v_pre_1188_ = lean_ctor_get(v_x_1173_, 0);
lean_inc(v_pre_1188_);
v_i_1189_ = lean_ctor_get(v_x_1173_, 1);
lean_inc(v_i_1189_);
lean_dec_ref_known(v_x_1173_, 2);
v_pre_1190_ = lean_ctor_get(v_x_1174_, 0);
lean_inc(v_pre_1190_);
v_i_1191_ = lean_ctor_get(v_x_1174_, 1);
lean_inc(v_i_1191_);
lean_dec_ref_known(v_x_1174_, 2);
v___x_1192_ = lean_apply_4(v_h__3_1177_, v_pre_1188_, v_i_1189_, v_pre_1190_, v_i_1191_);
return v___x_1192_;
}
else
{
lean_object* v___x_1193_; 
lean_dec(v_h__3_1177_);
v___x_1193_ = lean_apply_5(v_h__4_1178_, v_x_1173_, v_x_1174_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1193_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Name_instDecidableEq(lean_object* v_a_1194_, lean_object* v_b_1195_){
_start:
{
uint8_t v___x_1196_; 
v___x_1196_ = lean_name_eq(v_a_1194_, v_b_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object* v_a_1197_, lean_object* v_b_1198_){
_start:
{
uint8_t v_res_1199_; lean_object* v_r_1200_; 
v_res_1199_ = l_Lean_Name_instDecidableEq(v_a_1197_, v_b_1198_);
lean_dec(v_b_1198_);
lean_dec(v_a_1197_);
v_r_1200_ = lean_box(v_res_1199_);
return v_r_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object* v_g_1201_){
_start:
{
lean_object* v_namePrefix_1202_; lean_object* v_idx_1203_; lean_object* v___x_1204_; 
v_namePrefix_1202_ = lean_ctor_get(v_g_1201_, 0);
lean_inc(v_namePrefix_1202_);
v_idx_1203_ = lean_ctor_get(v_g_1201_, 1);
lean_inc(v_idx_1203_);
lean_dec_ref(v_g_1201_);
v___x_1204_ = l_Lean_Name_num___override(v_namePrefix_1202_, v_idx_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object* v_g_1205_){
_start:
{
lean_object* v_namePrefix_1206_; lean_object* v_idx_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1216_; 
v_namePrefix_1206_ = lean_ctor_get(v_g_1205_, 0);
v_idx_1207_ = lean_ctor_get(v_g_1205_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_g_1205_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1209_ = v_g_1205_;
v_isShared_1210_ = v_isSharedCheck_1216_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_idx_1207_);
lean_inc(v_namePrefix_1206_);
lean_dec(v_g_1205_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1216_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1211_ = lean_unsigned_to_nat(1u);
v___x_1212_ = lean_nat_add(v_idx_1207_, v___x_1211_);
lean_dec(v_idx_1207_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v___x_1212_);
v___x_1214_ = v___x_1209_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_namePrefix_1206_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object* v_g_1217_){
_start:
{
lean_object* v_namePrefix_1218_; lean_object* v_idx_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1231_; 
v_namePrefix_1218_ = lean_ctor_get(v_g_1217_, 0);
v_idx_1219_ = lean_ctor_get(v_g_1217_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_g_1217_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1221_ = v_g_1217_;
v_isShared_1222_ = v_isSharedCheck_1231_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_idx_1219_);
lean_inc(v_namePrefix_1218_);
lean_dec(v_g_1217_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1231_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
lean_inc(v_idx_1219_);
lean_inc(v_namePrefix_1218_);
v___x_1223_ = l_Lean_Name_num___override(v_namePrefix_1218_, v_idx_1219_);
v___x_1224_ = lean_unsigned_to_nat(1u);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v___x_1224_);
lean_ctor_set(v___x_1221_, 0, v___x_1223_);
v___x_1226_ = v___x_1221_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = lean_nat_add(v_idx_1219_, v___x_1224_);
lean_dec(v_idx_1219_);
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_namePrefix_1218_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1226_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
return v___x_1229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object* v_toPure_1232_, lean_object* v_r_1233_, lean_object* v_____r_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_apply_2(v_toPure_1232_, lean_box(0), v_r_1233_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object* v_toPure_1236_, lean_object* v_setNGen_1237_, lean_object* v_toBind_1238_, lean_object* v_ngen_1239_){
_start:
{
lean_object* v_namePrefix_1240_; lean_object* v_idx_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1254_; 
v_namePrefix_1240_ = lean_ctor_get(v_ngen_1239_, 0);
v_idx_1241_ = lean_ctor_get(v_ngen_1239_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_ngen_1239_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1243_ = v_ngen_1239_;
v_isShared_1244_ = v_isSharedCheck_1254_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_idx_1241_);
lean_inc(v_namePrefix_1240_);
lean_dec(v_ngen_1239_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1254_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_r_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
lean_inc(v_idx_1241_);
lean_inc(v_namePrefix_1240_);
v_r_1245_ = l_Lean_Name_num___override(v_namePrefix_1240_, v_idx_1241_);
v___f_1246_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1246_, 0, v_toPure_1236_);
lean_closure_set(v___f_1246_, 1, v_r_1245_);
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = lean_nat_add(v_idx_1241_, v___x_1247_);
lean_dec(v_idx_1241_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___x_1248_);
v___x_1250_ = v___x_1243_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_namePrefix_1240_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_apply_1(v_setNGen_1237_, v___x_1250_);
v___x_1252_ = lean_apply_4(v_toBind_1238_, lean_box(0), lean_box(0), v___x_1251_, v___f_1246_);
return v___x_1252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object* v_inst_1255_, lean_object* v_inst_1256_){
_start:
{
lean_object* v_toApplicative_1257_; lean_object* v_toBind_1258_; lean_object* v_getNGen_1259_; lean_object* v_setNGen_1260_; lean_object* v_toPure_1261_; lean_object* v___f_1262_; lean_object* v___x_1263_; 
v_toApplicative_1257_ = lean_ctor_get(v_inst_1255_, 0);
lean_inc_ref(v_toApplicative_1257_);
v_toBind_1258_ = lean_ctor_get(v_inst_1255_, 1);
lean_inc_n(v_toBind_1258_, 2);
lean_dec_ref(v_inst_1255_);
v_getNGen_1259_ = lean_ctor_get(v_inst_1256_, 0);
lean_inc(v_getNGen_1259_);
v_setNGen_1260_ = lean_ctor_get(v_inst_1256_, 1);
lean_inc(v_setNGen_1260_);
lean_dec_ref(v_inst_1256_);
v_toPure_1261_ = lean_ctor_get(v_toApplicative_1257_, 1);
lean_inc(v_toPure_1261_);
lean_dec_ref(v_toApplicative_1257_);
v___f_1262_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1262_, 0, v_toPure_1261_);
lean_closure_set(v___f_1262_, 1, v_setNGen_1260_);
lean_closure_set(v___f_1262_, 2, v_toBind_1258_);
v___x_1263_ = lean_apply_4(v_toBind_1258_, lean_box(0), lean_box(0), v_getNGen_1259_, v___f_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object* v_m_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_mkFreshId___redArg(v_inst_1265_, v_inst_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object* v_setNGen_1268_, lean_object* v_inst_1269_, lean_object* v_ngen_1270_){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_apply_1(v_setNGen_1268_, v_ngen_1270_);
v___x_1272_ = lean_apply_2(v_inst_1269_, lean_box(0), v___x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object* v_inst_1273_, lean_object* v_inst_1274_){
_start:
{
lean_object* v_getNGen_1275_; lean_object* v_setNGen_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1285_; 
v_getNGen_1275_ = lean_ctor_get(v_inst_1274_, 0);
v_setNGen_1276_ = lean_ctor_get(v_inst_1274_, 1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_inst_1274_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1278_ = v_inst_1274_;
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_setNGen_1276_);
lean_inc(v_getNGen_1275_);
lean_dec(v_inst_1274_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___f_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
lean_inc(v_inst_1273_);
v___f_1280_ = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1280_, 0, v_setNGen_1276_);
lean_closure_set(v___f_1280_, 1, v_inst_1273_);
v___x_1281_ = lean_apply_2(v_inst_1273_, lean_box(0), v_getNGen_1275_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v___f_1280_);
lean_ctor_set(v___x_1278_, 0, v___x_1281_);
v___x_1283_ = v___x_1278_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___f_1280_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object* v_m_1286_, lean_object* v_n_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_monadNameGeneratorLift___redArg(v_inst_1288_, v_inst_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_){
_start:
{
if (lean_obj_tag(v_x_1293_) == 0)
{
lean_dec(v_x_1291_);
return v_x_1292_;
}
else
{
lean_object* v_head_1294_; lean_object* v_tail_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1306_; 
v_head_1294_ = lean_ctor_get(v_x_1293_, 0);
v_tail_1295_ = lean_ctor_get(v_x_1293_, 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_x_1293_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1297_ = v_x_1293_;
v_isShared_1298_ = v_isSharedCheck_1306_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_tail_1295_);
lean_inc(v_head_1294_);
lean_dec(v_x_1293_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1306_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
lean_inc(v_x_1291_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set_tag(v___x_1297_, 5);
lean_ctor_set(v___x_1297_, 1, v_x_1291_);
lean_ctor_set(v___x_1297_, 0, v_x_1292_);
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_x_1292_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_x_1291_);
v___x_1300_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = l_String_quote(v_head_1294_);
v___x_1302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
v___x_1303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1300_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v_x_1292_ = v___x_1303_;
v_x_1293_ = v_tail_1295_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object* v_x_1307_, lean_object* v_x_1308_, lean_object* v_x_1309_){
_start:
{
if (lean_obj_tag(v_x_1309_) == 0)
{
lean_dec(v_x_1307_);
return v_x_1308_;
}
else
{
lean_object* v_head_1310_; lean_object* v_tail_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1322_; 
v_head_1310_ = lean_ctor_get(v_x_1309_, 0);
v_tail_1311_ = lean_ctor_get(v_x_1309_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_x_1309_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1313_ = v_x_1309_;
v_isShared_1314_ = v_isSharedCheck_1322_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_tail_1311_);
lean_inc(v_head_1310_);
lean_dec(v_x_1309_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1322_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
lean_inc(v_x_1307_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set_tag(v___x_1313_, 5);
lean_ctor_set(v___x_1313_, 1, v_x_1307_);
lean_ctor_set(v___x_1313_, 0, v_x_1308_);
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_x_1308_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_x_1307_);
v___x_1316_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1317_ = l_String_quote(v_head_1310_);
v___x_1318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
v___x_1319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1316_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(v_x_1307_, v___x_1319_, v_tail_1311_);
return v___x_1320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = l_String_quote(v___y_1323_);
v___x_1325_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object* v_x_1326_, lean_object* v_x_1327_){
_start:
{
if (lean_obj_tag(v_x_1326_) == 0)
{
lean_object* v___x_1328_; 
lean_dec(v_x_1327_);
v___x_1328_ = lean_box(0);
return v___x_1328_;
}
else
{
lean_object* v_tail_1329_; 
v_tail_1329_ = lean_ctor_get(v_x_1326_, 1);
if (lean_obj_tag(v_tail_1329_) == 0)
{
lean_object* v_head_1330_; lean_object* v___x_1331_; 
lean_dec(v_x_1327_);
v_head_1330_ = lean_ctor_get(v_x_1326_, 0);
lean_inc(v_head_1330_);
lean_dec_ref_known(v_x_1326_, 2);
v___x_1331_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1330_);
return v___x_1331_;
}
else
{
lean_object* v_head_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_inc(v_tail_1329_);
v_head_1332_ = lean_ctor_get(v_x_1326_, 0);
lean_inc(v_head_1332_);
lean_dec_ref_known(v_x_1326_, 2);
v___x_1333_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1332_);
v___x_1334_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(v_x_1327_, v___x_1333_, v_tail_1329_);
return v___x_1334_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2));
v___x_1347_ = lean_string_length(v___x_1346_);
return v___x_1347_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7);
v___x_1349_ = lean_nat_to_int(v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object* v_a_1354_){
_start:
{
if (lean_obj_tag(v_a_1354_) == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1355_;
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1356_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1357_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(v_a_1354_, v___x_1356_);
v___x_1358_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1359_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v___x_1357_);
v___x_1361_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1360_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1358_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = l_Std_Format_fill(v___x_1363_);
return v___x_1364_;
}
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_unsigned_to_nat(2u);
v___x_1372_ = lean_nat_to_int(v___x_1371_);
return v___x_1372_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = lean_nat_to_int(v___x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object* v_x_1381_, lean_object* v_prec_1382_){
_start:
{
if (lean_obj_tag(v_x_1381_) == 0)
{
lean_object* v_ns_1383_; lean_object* v___y_1385_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_ns_1383_ = lean_ctor_get(v_x_1381_, 0);
lean_inc(v_ns_1383_);
lean_dec_ref_known(v_x_1381_, 1);
v___x_1394_ = lean_unsigned_to_nat(1024u);
v___x_1395_ = lean_nat_dec_le(v___x_1394_, v_prec_1382_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1385_ = v___x_1396_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1385_ = v___x_1397_;
goto v___jp_1384_;
}
v___jp_1384_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1386_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__2));
v___x_1387_ = lean_unsigned_to_nat(1024u);
v___x_1388_ = l_Lean_Name_reprPrec(v_ns_1383_, v___x_1387_);
v___x_1389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1386_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
lean_inc(v___y_1385_);
v___x_1390_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___y_1385_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = 0;
v___x_1392_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1392_, 0, v___x_1390_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*1, v___x_1391_);
v___x_1393_ = l_Repr_addAppParen(v___x_1392_, v_prec_1382_);
return v___x_1393_;
}
}
else
{
lean_object* v_n_1398_; lean_object* v_fields_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1423_; 
v_n_1398_ = lean_ctor_get(v_x_1381_, 0);
v_fields_1399_ = lean_ctor_get(v_x_1381_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1401_ = v_x_1381_;
v_isShared_1402_ = v_isSharedCheck_1423_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_fields_1399_);
lean_inc(v_n_1398_);
lean_dec(v_x_1381_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1423_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___y_1404_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = lean_unsigned_to_nat(1024u);
v___x_1420_ = lean_nat_dec_le(v___x_1419_, v_prec_1382_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1404_ = v___x_1421_;
goto v___jp_1403_;
}
else
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1404_ = v___x_1422_;
goto v___jp_1403_;
}
v___jp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1405_ = lean_box(1);
v___x_1406_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__7));
v___x_1407_ = lean_unsigned_to_nat(1024u);
v___x_1408_ = l_Lean_Name_reprPrec(v_n_1398_, v___x_1407_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 5);
lean_ctor_set(v___x_1401_, 1, v___x_1408_);
lean_ctor_set(v___x_1401_, 0, v___x_1406_);
v___x_1410_ = v___x_1401_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v___x_1405_);
v___x_1412_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_fields_1399_);
v___x_1413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
lean_inc(v___y_1404_);
v___x_1414_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___y_1404_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = 0;
v___x_1416_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set_uint8(v___x_1416_, sizeof(void*)*1, v___x_1415_);
v___x_1417_ = l_Repr_addAppParen(v___x_1416_, v_prec_1382_);
return v___x_1417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object* v_x_1424_, lean_object* v_prec_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_Syntax_instReprPreresolved_repr(v_x_1424_, v_prec_1425_);
lean_dec(v_prec_1425_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object* v_a_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_nat_to_int(v_a_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object* v_a_1429_, lean_object* v_n_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_a_1429_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object* v_a_1432_, lean_object* v_n_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(v_a_1432_, v_n_1433_);
lean_dec(v_n_1433_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = lean_unsigned_to_nat(0u);
v___x_1439_ = l_Lean_Syntax_instReprPreresolved_repr(v___y_1437_, v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_){
_start:
{
if (lean_obj_tag(v_x_1442_) == 0)
{
lean_dec(v_x_1440_);
return v_x_1441_;
}
else
{
lean_object* v_head_1443_; lean_object* v_tail_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1455_; 
v_head_1443_ = lean_ctor_get(v_x_1442_, 0);
v_tail_1444_ = lean_ctor_get(v_x_1442_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_x_1442_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1446_ = v_x_1442_;
v_isShared_1447_ = v_isSharedCheck_1455_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_tail_1444_);
lean_inc(v_head_1443_);
lean_dec(v_x_1442_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1455_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
lean_inc(v_x_1440_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set_tag(v___x_1446_, 5);
lean_ctor_set(v___x_1446_, 1, v_x_1440_);
lean_ctor_set(v___x_1446_, 0, v_x_1441_);
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_x_1441_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_x_1440_);
v___x_1449_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1450_ = lean_unsigned_to_nat(0u);
v___x_1451_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1443_, v___x_1450_);
v___x_1452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1449_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v_x_1441_ = v___x_1452_;
v_x_1442_ = v_tail_1444_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object* v_x_1456_, lean_object* v_x_1457_, lean_object* v_x_1458_){
_start:
{
if (lean_obj_tag(v_x_1458_) == 0)
{
lean_dec(v_x_1456_);
return v_x_1457_;
}
else
{
lean_object* v_head_1459_; lean_object* v_tail_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1471_; 
v_head_1459_ = lean_ctor_get(v_x_1458_, 0);
v_tail_1460_ = lean_ctor_get(v_x_1458_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_x_1458_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1462_ = v_x_1458_;
v_isShared_1463_ = v_isSharedCheck_1471_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_tail_1460_);
lean_inc(v_head_1459_);
lean_dec(v_x_1458_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1471_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
lean_inc(v_x_1456_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set_tag(v___x_1462_, 5);
lean_ctor_set(v___x_1462_, 1, v_x_1456_);
lean_ctor_set(v___x_1462_, 0, v_x_1457_);
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_x_1457_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_x_1456_);
v___x_1465_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1459_, v___x_1466_);
v___x_1468_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1465_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(v_x_1456_, v___x_1468_, v_tail_1460_);
return v___x_1469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object* v_x_1472_, lean_object* v_x_1473_){
_start:
{
if (lean_obj_tag(v_x_1472_) == 0)
{
lean_object* v___x_1474_; 
lean_dec(v_x_1473_);
v___x_1474_ = lean_box(0);
return v___x_1474_;
}
else
{
lean_object* v_tail_1475_; 
v_tail_1475_ = lean_ctor_get(v_x_1472_, 1);
if (lean_obj_tag(v_tail_1475_) == 0)
{
lean_object* v_head_1476_; lean_object* v___x_1477_; 
lean_dec(v_x_1473_);
v_head_1476_ = lean_ctor_get(v_x_1472_, 0);
lean_inc(v_head_1476_);
lean_dec_ref_known(v_x_1472_, 2);
v___x_1477_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1476_);
return v___x_1477_;
}
else
{
lean_object* v_head_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_inc(v_tail_1475_);
v_head_1478_ = lean_ctor_get(v_x_1472_, 0);
lean_inc(v_head_1478_);
lean_dec_ref_known(v_x_1472_, 2);
v___x_1479_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1478_);
v___x_1480_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(v_x_1473_, v___x_1479_, v_tail_1475_);
return v___x_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object* v_a_1481_){
_start:
{
if (lean_obj_tag(v_a_1481_) == 0)
{
lean_object* v___x_1482_; 
v___x_1482_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; lean_object* v___x_1492_; 
v___x_1483_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1484_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(v_a_1481_, v___x_1483_);
v___x_1485_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1486_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v___x_1484_);
v___x_1488_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1485_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = 0;
v___x_1492_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1492_, 0, v___x_1490_);
lean_ctor_set_uint8(v___x_1492_, sizeof(void*)*1, v___x_1491_);
return v___x_1492_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1502_, lean_object* v_x_1503_, lean_object* v_x_1504_){
_start:
{
if (lean_obj_tag(v_x_1504_) == 0)
{
lean_dec(v_x_1502_);
return v_x_1503_;
}
else
{
lean_object* v_head_1505_; lean_object* v_tail_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1517_; 
v_head_1505_ = lean_ctor_get(v_x_1504_, 0);
v_tail_1506_ = lean_ctor_get(v_x_1504_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_x_1504_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1508_ = v_x_1504_;
v_isShared_1509_ = v_isSharedCheck_1517_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_tail_1506_);
lean_inc(v_head_1505_);
lean_dec(v_x_1504_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1517_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
lean_inc(v_x_1502_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 5);
lean_ctor_set(v___x_1508_, 1, v_x_1502_);
lean_ctor_set(v___x_1508_, 0, v_x_1503_);
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_x_1503_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_x_1502_);
v___x_1511_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = l_Lean_Syntax_instRepr_repr(v_head_1505_, v___x_1512_);
v___x_1514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1511_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v_x_1503_ = v___x_1514_;
v_x_1504_ = v_tail_1506_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object* v_x_1518_, lean_object* v_x_1519_, lean_object* v_x_1520_){
_start:
{
if (lean_obj_tag(v_x_1520_) == 0)
{
lean_dec(v_x_1518_);
return v_x_1519_;
}
else
{
lean_object* v_head_1521_; lean_object* v_tail_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1533_; 
v_head_1521_ = lean_ctor_get(v_x_1520_, 0);
v_tail_1522_ = lean_ctor_get(v_x_1520_, 1);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_x_1520_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1524_ = v_x_1520_;
v_isShared_1525_ = v_isSharedCheck_1533_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_tail_1522_);
lean_inc(v_head_1521_);
lean_dec(v_x_1520_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1533_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
lean_inc(v_x_1518_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set_tag(v___x_1524_, 5);
lean_ctor_set(v___x_1524_, 1, v_x_1518_);
lean_ctor_set(v___x_1524_, 0, v_x_1519_);
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_x_1519_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_x_1518_);
v___x_1527_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1528_ = lean_unsigned_to_nat(0u);
v___x_1529_ = l_Lean_Syntax_instRepr_repr(v_head_1521_, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1527_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(v_x_1518_, v___x_1530_, v_tail_1522_);
return v___x_1531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object* v_x_1534_, lean_object* v_x_1535_){
_start:
{
if (lean_obj_tag(v_x_1534_) == 0)
{
lean_object* v___x_1536_; 
lean_dec(v_x_1535_);
v___x_1536_ = lean_box(0);
return v___x_1536_;
}
else
{
lean_object* v_tail_1537_; 
v_tail_1537_ = lean_ctor_get(v_x_1534_, 1);
if (lean_obj_tag(v_tail_1537_) == 0)
{
lean_object* v_head_1538_; lean_object* v___x_1539_; 
lean_dec(v_x_1535_);
v_head_1538_ = lean_ctor_get(v_x_1534_, 0);
lean_inc(v_head_1538_);
lean_dec_ref_known(v_x_1534_, 2);
v___x_1539_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1538_);
return v___x_1539_;
}
else
{
lean_object* v_head_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_inc(v_tail_1537_);
v_head_1540_ = lean_ctor_get(v_x_1534_, 0);
lean_inc(v_head_1540_);
lean_dec_ref_known(v_x_1534_, 2);
v___x_1541_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1540_);
v___x_1542_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(v_x_1535_, v___x_1541_, v_tail_1537_);
return v___x_1542_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0));
v___x_1545_ = lean_string_length(v___x_1544_);
return v___x_1545_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1);
v___x_1547_ = lean_nat_to_int(v___x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object* v_xs_1553_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1554_ = lean_array_get_size(v_xs_1553_);
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_nat_dec_eq(v___x_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1557_ = lean_array_to_list(v_xs_1553_);
v___x_1558_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1559_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(v___x_1557_, v___x_1558_);
v___x_1560_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2);
v___x_1561_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3));
v___x_1562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v___x_1559_);
v___x_1563_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1560_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = l_Std_Format_fill(v___x_1565_);
return v___x_1566_;
}
else
{
lean_object* v___x_1567_; 
lean_dec_ref(v_xs_1553_);
v___x_1567_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5));
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object* v_x_1581_, lean_object* v_prec_1582_){
_start:
{
lean_object* v___y_1584_; 
switch(lean_obj_tag(v_x_1581_))
{
case 0:
{
lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1590_ = lean_unsigned_to_nat(1024u);
v___x_1591_ = lean_nat_dec_le(v___x_1590_, v_prec_1582_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1584_ = v___x_1592_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1584_ = v___x_1593_;
goto v___jp_1583_;
}
}
case 1:
{
lean_object* v_info_1594_; lean_object* v_kind_1595_; lean_object* v_args_1596_; lean_object* v___y_1598_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v_info_1594_ = lean_ctor_get(v_x_1581_, 0);
lean_inc(v_info_1594_);
v_kind_1595_ = lean_ctor_get(v_x_1581_, 1);
lean_inc(v_kind_1595_);
v_args_1596_ = lean_ctor_get(v_x_1581_, 2);
lean_inc_ref(v_args_1596_);
lean_dec_ref_known(v_x_1581_, 3);
v___x_1614_ = lean_unsigned_to_nat(1024u);
v___x_1615_ = lean_nat_dec_le(v___x_1614_, v_prec_1582_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1598_ = v___x_1616_;
goto v___jp_1597_;
}
else
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1598_ = v___x_1617_;
goto v___jp_1597_;
}
v___jp_1597_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1599_ = lean_box(1);
v___x_1600_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__4));
v___x_1601_ = lean_unsigned_to_nat(1024u);
v___x_1602_ = l_instReprSourceInfo_repr(v_info_1594_, v___x_1601_);
v___x_1603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1600_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v___x_1599_);
v___x_1605_ = l_Lean_Name_reprPrec(v_kind_1595_, v___x_1601_);
v___x_1606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
lean_ctor_set(v___x_1607_, 1, v___x_1599_);
v___x_1608_ = l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(v_args_1596_);
v___x_1609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
lean_inc(v___y_1598_);
v___x_1610_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___y_1598_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = 0;
v___x_1612_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set_uint8(v___x_1612_, sizeof(void*)*1, v___x_1611_);
v___x_1613_ = l_Repr_addAppParen(v___x_1612_, v_prec_1582_);
return v___x_1613_;
}
}
case 2:
{
lean_object* v_info_1618_; lean_object* v_val_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1644_; 
v_info_1618_ = lean_ctor_get(v_x_1581_, 0);
v_val_1619_ = lean_ctor_get(v_x_1581_, 1);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_x_1581_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1621_ = v_x_1581_;
v_isShared_1622_ = v_isSharedCheck_1644_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_val_1619_);
lean_inc(v_info_1618_);
lean_dec(v_x_1581_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1644_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___y_1624_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1640_ = lean_unsigned_to_nat(1024u);
v___x_1641_ = lean_nat_dec_le(v___x_1640_, v_prec_1582_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; 
v___x_1642_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1624_ = v___x_1642_;
goto v___jp_1623_;
}
else
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1624_ = v___x_1643_;
goto v___jp_1623_;
}
v___jp_1623_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1625_ = lean_box(1);
v___x_1626_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__7));
v___x_1627_ = lean_unsigned_to_nat(1024u);
v___x_1628_ = l_instReprSourceInfo_repr(v_info_1618_, v___x_1627_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set_tag(v___x_1621_, 5);
lean_ctor_set(v___x_1621_, 1, v___x_1628_);
lean_ctor_set(v___x_1621_, 0, v___x_1626_);
v___x_1630_ = v___x_1621_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v___x_1625_);
v___x_1632_ = l_String_quote(v_val_1619_);
v___x_1633_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
v___x_1634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1631_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
lean_inc(v___y_1624_);
v___x_1635_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___y_1624_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = 0;
v___x_1637_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set_uint8(v___x_1637_, sizeof(void*)*1, v___x_1636_);
v___x_1638_ = l_Repr_addAppParen(v___x_1637_, v_prec_1582_);
return v___x_1638_;
}
}
}
}
default: 
{
lean_object* v_info_1645_; lean_object* v_rawVal_1646_; lean_object* v_val_1647_; lean_object* v_preresolved_1648_; lean_object* v___y_1650_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
v_info_1645_ = lean_ctor_get(v_x_1581_, 0);
lean_inc(v_info_1645_);
v_rawVal_1646_ = lean_ctor_get(v_x_1581_, 1);
lean_inc_ref(v_rawVal_1646_);
v_val_1647_ = lean_ctor_get(v_x_1581_, 2);
lean_inc(v_val_1647_);
v_preresolved_1648_ = lean_ctor_get(v_x_1581_, 3);
lean_inc(v_preresolved_1648_);
lean_dec_ref_known(v_x_1581_, 4);
v___x_1673_ = lean_unsigned_to_nat(1024u);
v___x_1674_ = lean_nat_dec_le(v___x_1673_, v_prec_1582_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1650_ = v___x_1675_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1650_ = v___x_1676_;
goto v___jp_1649_;
}
v___jp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1651_ = lean_box(1);
v___x_1652_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__10));
v___x_1653_ = lean_unsigned_to_nat(1024u);
v___x_1654_ = l_instReprSourceInfo_repr(v_info_1645_, v___x_1653_);
v___x_1655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1652_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v___x_1651_);
v___x_1657_ = lean_substring_tostring(v_rawVal_1646_);
v___x_1658_ = l_String_quote(v___x_1657_);
v___x_1659_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__11));
v___x_1660_ = lean_string_append(v___x_1658_, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
v___x_1662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1656_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
lean_ctor_set(v___x_1663_, 1, v___x_1651_);
v___x_1664_ = l_Lean_Name_reprPrec(v_val_1647_, v___x_1653_);
v___x_1665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
lean_ctor_set(v___x_1666_, 1, v___x_1651_);
v___x_1667_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_preresolved_1648_);
v___x_1668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
lean_inc(v___y_1650_);
v___x_1669_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___y_1650_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = 0;
v___x_1671_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set_uint8(v___x_1671_, sizeof(void*)*1, v___x_1670_);
v___x_1672_ = l_Repr_addAppParen(v___x_1671_, v_prec_1582_);
return v___x_1672_;
}
}
}
v___jp_1583_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1585_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__1));
lean_inc(v___y_1584_);
v___x_1586_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___y_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = 0;
v___x_1588_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*1, v___x_1587_);
v___x_1589_ = l_Repr_addAppParen(v___x_1588_, v_prec_1582_);
return v___x_1589_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_unsigned_to_nat(0u);
v___x_1679_ = l_Lean_Syntax_instRepr_repr(v___y_1677_, v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object* v_x_1680_, lean_object* v_prec_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Syntax_instRepr_repr(v_x_1680_, v_prec_1681_);
lean_dec(v_prec_1681_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object* v_a_1683_, lean_object* v_n_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_a_1683_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object* v_a_1686_, lean_object* v_n_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(v_a_1686_, v_n_1687_);
lean_dec(v_n_1687_);
return v_res_1688_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_unsigned_to_nat(7u);
v___x_1705_ = lean_nat_to_int(v___x_1704_);
return v___x_1705_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0));
v___x_1708_ = lean_string_length(v___x_1707_);
return v___x_1708_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9);
v___x_1710_ = lean_nat_to_int(v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object* v_x_1715_){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1716_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6));
v___x_1717_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_1718_ = lean_unsigned_to_nat(0u);
v___x_1719_ = l_Lean_Syntax_instRepr_repr(v_x_1715_, v___x_1718_);
v___x_1720_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1717_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = 0;
v___x_1722_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1722_, 0, v___x_1720_);
lean_ctor_set_uint8(v___x_1722_, sizeof(void*)*1, v___x_1721_);
v___x_1723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1716_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_1725_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_1726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
lean_ctor_set(v___x_1726_, 1, v___x_1723_);
v___x_1727_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_1728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1726_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1724_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set_uint8(v___x_1730_, sizeof(void*)*1, v___x_1721_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object* v_ks_1731_, lean_object* v_x_1732_, lean_object* v_prec_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_x_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object* v_ks_1735_, lean_object* v_x_1736_, lean_object* v_prec_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Syntax_instReprTSyntax_repr(v_ks_1735_, v_x_1736_, v_prec_1737_);
lean_dec(v_prec_1737_);
lean_dec(v_ks_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object* v_ks_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_alloc_closure((void*)(l_Lean_Syntax_instReprTSyntax_repr___boxed), 3, 1);
lean_closure_set(v___x_1740_, 0, v_ks_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0(lean_object* v_stx_1741_){
_start:
{
lean_inc(v_stx_1741_);
return v_stx_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0___boxed(lean_object* v_stx_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0(v_stx_1742_);
lean_dec(v_stx_1742_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object* v_k_1745_, lean_object* v_ks_1746_){
_start:
{
lean_object* v___f_1747_; 
v___f_1747_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0));
return v___f_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object* v_k_1748_, lean_object* v_ks_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(v_k_1748_, v_ks_1749_);
lean_dec(v_ks_1749_);
lean_dec(v_k_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object* v_ks_1751_, lean_object* v_k_x27_1752_){
_start:
{
lean_object* v___f_1753_; 
v___f_1753_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0));
return v___f_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object* v_ks_1754_, lean_object* v_k_x27_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind(v_ks_1754_, v_k_x27_1755_);
lean_dec(v_k_x27_1755_);
lean_dec(v_ks_1754_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object* v_s_1757_){
_start:
{
lean_inc(v_s_1757_);
return v_s_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object* v_s_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_TSyntax_instCoeIdentTerm___lam__0(v_s_1758_);
lean_dec(v_s_1758_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object* v_info_1762_, lean_object* v_ss_1763_, lean_object* v_n_1764_, lean_object* v_res_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1766_, 0, v_info_1762_);
lean_ctor_set(v___x_1766_, 1, v_ss_1763_);
lean_ctor_set(v___x_1766_, 2, v_n_1764_);
lean_ctor_set(v___x_1766_, 3, v_res_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object* v_k_1775_){
_start:
{
lean_object* v___f_1776_; 
v___f_1776_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object* v_k_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_TSyntax_Compat_instCoeTailSyntax(v_k_1777_);
lean_dec(v_k_1777_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object* v_k_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_alloc_closure((void*)(l_Lean_TSyntaxArray_mkImpl___boxed), 2, 1);
lean_closure_set(v___x_1780_, 0, v_k_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object* v_x_1781_, lean_object* v_x_1782_){
_start:
{
if (lean_obj_tag(v_x_1781_) == 0)
{
if (lean_obj_tag(v_x_1782_) == 0)
{
uint8_t v___x_1783_; 
v___x_1783_ = 1;
return v___x_1783_;
}
else
{
uint8_t v___x_1784_; 
v___x_1784_ = 0;
return v___x_1784_;
}
}
else
{
if (lean_obj_tag(v_x_1782_) == 0)
{
uint8_t v___x_1785_; 
v___x_1785_ = 0;
return v___x_1785_;
}
else
{
lean_object* v_head_1786_; lean_object* v_tail_1787_; lean_object* v_head_1788_; lean_object* v_tail_1789_; uint8_t v___x_1790_; 
v_head_1786_ = lean_ctor_get(v_x_1781_, 0);
v_tail_1787_ = lean_ctor_get(v_x_1781_, 1);
v_head_1788_ = lean_ctor_get(v_x_1782_, 0);
v_tail_1789_ = lean_ctor_get(v_x_1782_, 1);
v___x_1790_ = lean_string_dec_eq(v_head_1786_, v_head_1788_);
if (v___x_1790_ == 0)
{
return v___x_1790_;
}
else
{
v_x_1781_ = v_tail_1787_;
v_x_1782_ = v_tail_1789_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object* v_x_1792_, lean_object* v_x_1793_){
_start:
{
uint8_t v_res_1794_; lean_object* v_r_1795_; 
v_res_1794_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_x_1792_, v_x_1793_);
lean_dec(v_x_1793_);
lean_dec(v_x_1792_);
v_r_1795_ = lean_box(v_res_1794_);
return v_r_1795_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object* v_x_1796_, lean_object* v_x_1797_){
_start:
{
if (lean_obj_tag(v_x_1796_) == 0)
{
if (lean_obj_tag(v_x_1797_) == 0)
{
lean_object* v_ns_1798_; lean_object* v_ns_1799_; uint8_t v___x_1800_; 
v_ns_1798_ = lean_ctor_get(v_x_1796_, 0);
v_ns_1799_ = lean_ctor_get(v_x_1797_, 0);
v___x_1800_ = lean_name_eq(v_ns_1798_, v_ns_1799_);
return v___x_1800_;
}
else
{
uint8_t v___x_1801_; 
v___x_1801_ = 0;
return v___x_1801_;
}
}
else
{
if (lean_obj_tag(v_x_1797_) == 1)
{
lean_object* v_n_1802_; lean_object* v_fields_1803_; lean_object* v_n_1804_; lean_object* v_fields_1805_; uint8_t v___x_1806_; 
v_n_1802_ = lean_ctor_get(v_x_1796_, 0);
v_fields_1803_ = lean_ctor_get(v_x_1796_, 1);
v_n_1804_ = lean_ctor_get(v_x_1797_, 0);
v_fields_1805_ = lean_ctor_get(v_x_1797_, 1);
v___x_1806_ = lean_name_eq(v_n_1802_, v_n_1804_);
if (v___x_1806_ == 0)
{
return v___x_1806_;
}
else
{
uint8_t v___x_1807_; 
v___x_1807_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_fields_1803_, v_fields_1805_);
return v___x_1807_;
}
}
else
{
uint8_t v___x_1808_; 
v___x_1808_ = 0;
return v___x_1808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object* v_x_1809_, lean_object* v_x_1810_){
_start:
{
uint8_t v_res_1811_; lean_object* v_r_1812_; 
v_res_1811_ = l_Lean_Syntax_instBEqPreresolved_beq(v_x_1809_, v_x_1810_);
lean_dec_ref(v_x_1810_);
lean_dec_ref(v_x_1809_);
v_r_1812_ = lean_box(v_res_1811_);
return v_r_1812_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object* v_x_1815_, lean_object* v_x_1816_){
_start:
{
if (lean_obj_tag(v_x_1815_) == 0)
{
if (lean_obj_tag(v_x_1816_) == 0)
{
uint8_t v___x_1817_; 
v___x_1817_ = 1;
return v___x_1817_;
}
else
{
uint8_t v___x_1818_; 
v___x_1818_ = 0;
return v___x_1818_;
}
}
else
{
if (lean_obj_tag(v_x_1816_) == 0)
{
uint8_t v___x_1819_; 
v___x_1819_ = 0;
return v___x_1819_;
}
else
{
lean_object* v_head_1820_; lean_object* v_tail_1821_; lean_object* v_head_1822_; lean_object* v_tail_1823_; uint8_t v___x_1824_; 
v_head_1820_ = lean_ctor_get(v_x_1815_, 0);
v_tail_1821_ = lean_ctor_get(v_x_1815_, 1);
v_head_1822_ = lean_ctor_get(v_x_1816_, 0);
v_tail_1823_ = lean_ctor_get(v_x_1816_, 1);
v___x_1824_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_1820_, v_head_1822_);
if (v___x_1824_ == 0)
{
return v___x_1824_;
}
else
{
v_x_1815_ = v_tail_1821_;
v_x_1816_ = v_tail_1823_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
uint8_t v_res_1828_; lean_object* v_r_1829_; 
v_res_1828_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_x_1826_, v_x_1827_);
lean_dec(v_x_1827_);
lean_dec(v_x_1826_);
v_r_1829_ = lean_box(v_res_1828_);
return v_r_1829_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structEq(lean_object* v_x_1830_, lean_object* v_x_1831_){
_start:
{
switch(lean_obj_tag(v_x_1830_))
{
case 0:
{
if (lean_obj_tag(v_x_1831_) == 0)
{
uint8_t v___x_1832_; 
v___x_1832_ = 1;
return v___x_1832_;
}
else
{
uint8_t v___x_1833_; 
lean_dec(v_x_1831_);
v___x_1833_ = 0;
return v___x_1833_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1831_) == 1)
{
lean_object* v_kind_1834_; lean_object* v_args_1835_; lean_object* v_kind_1836_; lean_object* v_args_1837_; uint8_t v___x_1838_; 
v_kind_1834_ = lean_ctor_get(v_x_1830_, 1);
lean_inc(v_kind_1834_);
v_args_1835_ = lean_ctor_get(v_x_1830_, 2);
lean_inc_ref(v_args_1835_);
lean_dec_ref_known(v_x_1830_, 3);
v_kind_1836_ = lean_ctor_get(v_x_1831_, 1);
lean_inc(v_kind_1836_);
v_args_1837_ = lean_ctor_get(v_x_1831_, 2);
lean_inc_ref(v_args_1837_);
lean_dec_ref_known(v_x_1831_, 3);
v___x_1838_ = lean_name_eq(v_kind_1834_, v_kind_1836_);
lean_dec(v_kind_1836_);
lean_dec(v_kind_1834_);
if (v___x_1838_ == 0)
{
lean_dec_ref(v_args_1837_);
lean_dec_ref(v_args_1835_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1839_ = lean_array_get_size(v_args_1835_);
v___x_1840_ = lean_array_get_size(v_args_1837_);
v___x_1841_ = lean_nat_dec_eq(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_dec_ref(v_args_1837_);
lean_dec_ref(v_args_1835_);
return v___x_1841_;
}
else
{
uint8_t v___x_1842_; 
v___x_1842_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_args_1835_, v_args_1837_, v___x_1839_);
lean_dec_ref(v_args_1837_);
lean_dec_ref(v_args_1835_);
return v___x_1842_;
}
}
}
else
{
uint8_t v___x_1843_; 
lean_dec_ref_known(v_x_1830_, 3);
lean_dec(v_x_1831_);
v___x_1843_ = 0;
return v___x_1843_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1831_) == 2)
{
lean_object* v_val_1844_; lean_object* v_val_1845_; uint8_t v___x_1846_; 
v_val_1844_ = lean_ctor_get(v_x_1830_, 1);
lean_inc_ref(v_val_1844_);
lean_dec_ref_known(v_x_1830_, 2);
v_val_1845_ = lean_ctor_get(v_x_1831_, 1);
lean_inc_ref(v_val_1845_);
lean_dec_ref_known(v_x_1831_, 2);
v___x_1846_ = lean_string_dec_eq(v_val_1844_, v_val_1845_);
lean_dec_ref(v_val_1845_);
lean_dec_ref(v_val_1844_);
return v___x_1846_;
}
else
{
uint8_t v___x_1847_; 
lean_dec_ref_known(v_x_1830_, 2);
lean_dec(v_x_1831_);
v___x_1847_ = 0;
return v___x_1847_;
}
}
default: 
{
if (lean_obj_tag(v_x_1831_) == 3)
{
lean_object* v_rawVal_1848_; lean_object* v_val_1849_; lean_object* v_preresolved_1850_; lean_object* v_rawVal_1851_; lean_object* v_val_1852_; lean_object* v_preresolved_1853_; uint8_t v___y_1855_; uint8_t v___x_1857_; 
v_rawVal_1848_ = lean_ctor_get(v_x_1830_, 1);
lean_inc_ref(v_rawVal_1848_);
v_val_1849_ = lean_ctor_get(v_x_1830_, 2);
lean_inc(v_val_1849_);
v_preresolved_1850_ = lean_ctor_get(v_x_1830_, 3);
lean_inc(v_preresolved_1850_);
lean_dec_ref_known(v_x_1830_, 4);
v_rawVal_1851_ = lean_ctor_get(v_x_1831_, 1);
lean_inc_ref(v_rawVal_1851_);
v_val_1852_ = lean_ctor_get(v_x_1831_, 2);
lean_inc(v_val_1852_);
v_preresolved_1853_ = lean_ctor_get(v_x_1831_, 3);
lean_inc(v_preresolved_1853_);
lean_dec_ref_known(v_x_1831_, 4);
v___x_1857_ = lean_substring_beq(v_rawVal_1848_, v_rawVal_1851_);
if (v___x_1857_ == 0)
{
lean_dec(v_val_1852_);
lean_dec(v_val_1849_);
v___y_1855_ = v___x_1857_;
goto v___jp_1854_;
}
else
{
uint8_t v___x_1858_; 
v___x_1858_ = lean_name_eq(v_val_1849_, v_val_1852_);
lean_dec(v_val_1852_);
lean_dec(v_val_1849_);
v___y_1855_ = v___x_1858_;
goto v___jp_1854_;
}
v___jp_1854_:
{
if (v___y_1855_ == 0)
{
lean_dec(v_preresolved_1853_);
lean_dec(v_preresolved_1850_);
return v___y_1855_;
}
else
{
uint8_t v___x_1856_; 
v___x_1856_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_preresolved_1850_, v_preresolved_1853_);
lean_dec(v_preresolved_1853_);
lean_dec(v_preresolved_1850_);
return v___x_1856_;
}
}
}
else
{
uint8_t v___x_1859_; 
lean_dec_ref_known(v_x_1830_, 4);
lean_dec(v_x_1831_);
v___x_1859_ = 0;
return v___x_1859_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object* v_xs_1860_, lean_object* v_ys_1861_, lean_object* v_x_1862_){
_start:
{
lean_object* v_zero_1863_; uint8_t v_isZero_1864_; 
v_zero_1863_ = lean_unsigned_to_nat(0u);
v_isZero_1864_ = lean_nat_dec_eq(v_x_1862_, v_zero_1863_);
if (v_isZero_1864_ == 1)
{
lean_dec(v_x_1862_);
return v_isZero_1864_;
}
else
{
lean_object* v_one_1865_; lean_object* v_n_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; 
v_one_1865_ = lean_unsigned_to_nat(1u);
v_n_1866_ = lean_nat_sub(v_x_1862_, v_one_1865_);
lean_dec(v_x_1862_);
v___x_1867_ = lean_array_fget_borrowed(v_xs_1860_, v_n_1866_);
v___x_1868_ = lean_array_fget_borrowed(v_ys_1861_, v_n_1866_);
lean_inc(v___x_1868_);
lean_inc(v___x_1867_);
v___x_1869_ = l_Lean_Syntax_structEq(v___x_1867_, v___x_1868_);
if (v___x_1869_ == 0)
{
lean_dec(v_n_1866_);
return v___x_1869_;
}
else
{
v_x_1862_ = v_n_1866_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object* v_xs_1871_, lean_object* v_ys_1872_, lean_object* v_x_1873_){
_start:
{
uint8_t v_res_1874_; lean_object* v_r_1875_; 
v_res_1874_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1871_, v_ys_1872_, v_x_1873_);
lean_dec_ref(v_ys_1872_);
lean_dec_ref(v_xs_1871_);
v_r_1875_ = lean_box(v_res_1874_);
return v_r_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object* v_x_1876_, lean_object* v_x_1877_){
_start:
{
uint8_t v_res_1878_; lean_object* v_r_1879_; 
v_res_1878_ = l_Lean_Syntax_structEq(v_x_1876_, v_x_1877_);
v_r_1879_ = lean_box(v_res_1878_);
return v_r_1879_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object* v_xs_1880_, lean_object* v_ys_1881_, lean_object* v_hsz_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
uint8_t v___x_1885_; 
v___x_1885_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1880_, v_ys_1881_, v_x_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object* v_xs_1886_, lean_object* v_ys_1887_, lean_object* v_hsz_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_){
_start:
{
uint8_t v_res_1891_; lean_object* v_r_1892_; 
v_res_1891_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(v_xs_1886_, v_ys_1887_, v_hsz_1888_, v_x_1889_, v_x_1890_);
lean_dec_ref(v_ys_1887_);
lean_dec_ref(v_xs_1886_);
v_r_1892_ = lean_box(v_res_1891_);
return v_r_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object* v_k_1895_){
_start:
{
lean_object* v___f_1896_; 
v___f_1896_ = ((lean_object*)(l_Lean_Syntax_instBEq___closed__0));
return v___f_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object* v_k_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_Syntax_instBEqTSyntax(v_k_1897_);
lean_dec(v_k_1897_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object* v_as_1899_, lean_object* v_i_1900_){
_start:
{
lean_object* v_zero_1901_; uint8_t v_isZero_1902_; 
v_zero_1901_ = lean_unsigned_to_nat(0u);
v_isZero_1902_ = lean_nat_dec_eq(v_i_1900_, v_zero_1901_);
if (v_isZero_1902_ == 1)
{
lean_object* v___x_1903_; 
lean_dec(v_i_1900_);
v___x_1903_ = lean_box(0);
return v___x_1903_;
}
else
{
lean_object* v_one_1904_; lean_object* v_n_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v_one_1904_ = lean_unsigned_to_nat(1u);
v_n_1905_ = lean_nat_sub(v_i_1900_, v_one_1904_);
lean_dec(v_i_1900_);
v___x_1906_ = lean_array_fget_borrowed(v_as_1899_, v_n_1905_);
v___x_1907_ = l_Lean_Syntax_getTailInfo_x3f(v___x_1906_);
if (lean_obj_tag(v___x_1907_) == 0)
{
v_i_1900_ = v_n_1905_;
goto _start;
}
else
{
lean_dec(v_n_1905_);
return v___x_1907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object* v_x_1909_){
_start:
{
switch(lean_obj_tag(v_x_1909_))
{
case 2:
{
lean_object* v_info_1910_; lean_object* v___x_1911_; 
v_info_1910_ = lean_ctor_get(v_x_1909_, 0);
lean_inc(v_info_1910_);
v___x_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1911_, 0, v_info_1910_);
return v___x_1911_;
}
case 3:
{
lean_object* v_info_1912_; lean_object* v___x_1913_; 
v_info_1912_ = lean_ctor_get(v_x_1909_, 0);
lean_inc(v_info_1912_);
v___x_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_info_1912_);
return v___x_1913_;
}
case 1:
{
lean_object* v_info_1914_; 
v_info_1914_ = lean_ctor_get(v_x_1909_, 0);
if (lean_obj_tag(v_info_1914_) == 2)
{
lean_object* v_args_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_args_1915_ = lean_ctor_get(v_x_1909_, 2);
v___x_1916_ = lean_array_get_size(v_args_1915_);
v___x_1917_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_args_1915_, v___x_1916_);
return v___x_1917_;
}
else
{
lean_object* v___x_1918_; 
lean_inc(v_info_1914_);
v___x_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1918_, 0, v_info_1914_);
return v___x_1918_;
}
}
default: 
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_box(0);
return v___x_1919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object* v_x_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_Syntax_getTailInfo_x3f(v_x_1920_);
lean_dec(v_x_1920_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object* v_as_1922_, lean_object* v_i_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1922_, v_i_1923_);
lean_dec_ref(v_as_1922_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object* v_as_1925_, lean_object* v_i_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1925_, v_i_1926_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object* v_as_1929_, lean_object* v_i_1930_, lean_object* v_a_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(v_as_1929_, v_i_1930_, v_a_1931_);
lean_dec_ref(v_as_1929_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object* v_stx_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1933_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_box(2);
return v___x_1935_;
}
else
{
lean_object* v_val_1936_; 
v_val_1936_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_val_1936_);
lean_dec_ref_known(v___x_1934_, 1);
return v_val_1936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object* v_stx_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_Syntax_getTailInfo(v_stx_1937_);
lean_dec(v_stx_1937_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object* v_stx_1939_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1939_);
if (lean_obj_tag(v___x_1940_) == 1)
{
lean_object* v_val_1941_; 
v_val_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_val_1941_);
lean_dec_ref_known(v___x_1940_, 1);
if (lean_obj_tag(v_val_1941_) == 0)
{
lean_object* v_trailing_1942_; lean_object* v_startPos_1943_; lean_object* v_stopPos_1944_; lean_object* v___x_1945_; 
v_trailing_1942_ = lean_ctor_get(v_val_1941_, 2);
lean_inc_ref(v_trailing_1942_);
lean_dec_ref_known(v_val_1941_, 4);
v_startPos_1943_ = lean_ctor_get(v_trailing_1942_, 1);
lean_inc(v_startPos_1943_);
v_stopPos_1944_ = lean_ctor_get(v_trailing_1942_, 2);
lean_inc(v_stopPos_1944_);
lean_dec_ref(v_trailing_1942_);
v___x_1945_ = lean_nat_sub(v_stopPos_1944_, v_startPos_1943_);
lean_dec(v_startPos_1943_);
lean_dec(v_stopPos_1944_);
return v___x_1945_;
}
else
{
lean_object* v___x_1946_; 
lean_dec(v_val_1941_);
v___x_1946_ = lean_unsigned_to_nat(0u);
return v___x_1946_;
}
}
else
{
lean_object* v___x_1947_; 
lean_dec(v___x_1940_);
v___x_1947_ = lean_unsigned_to_nat(0u);
return v___x_1947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object* v_stx_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Syntax_getTrailingSize(v_stx_1948_);
lean_dec(v_stx_1948_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object* v_stx_1950_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = l_Lean_Syntax_getTailInfo(v_stx_1950_);
v___x_1952_ = l_Lean_SourceInfo_getTrailing_x3f(v___x_1951_);
lean_dec(v___x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object* v_stx_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Syntax_getTrailing_x3f(v_stx_1953_);
lean_dec(v_stx_1953_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object* v_stx_1955_, uint8_t v_canonicalOnly_1956_){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = l_Lean_Syntax_getTailInfo(v_stx_1955_);
v___x_1958_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v___x_1957_, v_canonicalOnly_1956_);
lean_dec(v___x_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object* v_stx_1959_, lean_object* v_canonicalOnly_1960_){
_start:
{
uint8_t v_canonicalOnly_boxed_1961_; lean_object* v_res_1962_; 
v_canonicalOnly_boxed_1961_ = lean_unbox(v_canonicalOnly_1960_);
v_res_1962_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1959_, v_canonicalOnly_boxed_1961_);
lean_dec(v_stx_1959_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object* v_stx_1963_, uint8_t v_withLeading_1964_, uint8_t v_withTrailing_1965_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_Syntax_getHeadInfo(v_stx_1963_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_leading_1967_; lean_object* v_pos_1968_; lean_object* v___x_1969_; 
v_leading_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc_ref(v_leading_1967_);
v_pos_1968_ = lean_ctor_get(v___x_1966_, 1);
lean_inc(v_pos_1968_);
lean_dec_ref_known(v___x_1966_, 4);
v___x_1969_ = l_Lean_Syntax_getTailInfo(v_stx_1963_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_trailing_1970_; lean_object* v_endPos_1971_; lean_object* v_str_1972_; lean_object* v_startPos_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1987_; 
v_trailing_1970_ = lean_ctor_get(v___x_1969_, 2);
lean_inc_ref(v_trailing_1970_);
v_endPos_1971_ = lean_ctor_get(v___x_1969_, 3);
lean_inc(v_endPos_1971_);
lean_dec_ref_known(v___x_1969_, 4);
v_str_1972_ = lean_ctor_get(v_leading_1967_, 0);
v_startPos_1973_ = lean_ctor_get(v_leading_1967_, 1);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_leading_1967_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; 
v_unused_1988_ = lean_ctor_get(v_leading_1967_, 2);
lean_dec(v_unused_1988_);
v___x_1975_ = v_leading_1967_;
v_isShared_1976_ = v_isSharedCheck_1987_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_startPos_1973_);
lean_inc(v_str_1972_);
lean_dec(v_leading_1967_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1987_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1985_; 
if (v_withLeading_1964_ == 0)
{
lean_dec(v_startPos_1973_);
v___y_1985_ = v_pos_1968_;
goto v___jp_1984_;
}
else
{
lean_dec(v_pos_1968_);
v___y_1985_ = v_startPos_1973_;
goto v___jp_1984_;
}
v___jp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 2, v___y_1979_);
lean_ctor_set(v___x_1975_, 1, v___y_1978_);
v___x_1981_ = v___x_1975_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_str_1972_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v___y_1978_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v___y_1979_);
v___x_1981_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
return v___x_1982_;
}
}
v___jp_1984_:
{
if (v_withTrailing_1965_ == 0)
{
lean_dec_ref(v_trailing_1970_);
v___y_1978_ = v___y_1985_;
v___y_1979_ = v_endPos_1971_;
goto v___jp_1977_;
}
else
{
lean_object* v_stopPos_1986_; 
lean_dec(v_endPos_1971_);
v_stopPos_1986_ = lean_ctor_get(v_trailing_1970_, 2);
lean_inc(v_stopPos_1986_);
lean_dec_ref(v_trailing_1970_);
v___y_1978_ = v___y_1985_;
v___y_1979_ = v_stopPos_1986_;
goto v___jp_1977_;
}
}
}
}
else
{
lean_object* v___x_1989_; 
lean_dec(v___x_1969_);
lean_dec(v_pos_1968_);
lean_dec_ref(v_leading_1967_);
v___x_1989_ = lean_box(0);
return v___x_1989_;
}
}
else
{
lean_object* v___x_1990_; 
lean_dec(v___x_1966_);
v___x_1990_ = lean_box(0);
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object* v_stx_1991_, lean_object* v_withLeading_1992_, lean_object* v_withTrailing_1993_){
_start:
{
uint8_t v_withLeading_boxed_1994_; uint8_t v_withTrailing_boxed_1995_; lean_object* v_res_1996_; 
v_withLeading_boxed_1994_ = lean_unbox(v_withLeading_1992_);
v_withTrailing_boxed_1995_ = lean_unbox(v_withTrailing_1993_);
v_res_1996_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1991_, v_withLeading_boxed_1994_, v_withTrailing_boxed_1995_);
lean_dec(v_stx_1991_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object* v_a_1997_, lean_object* v_f_1998_, lean_object* v_i_1999_){
_start:
{
lean_object* v_zero_2000_; uint8_t v_isZero_2001_; 
v_zero_2000_ = lean_unsigned_to_nat(0u);
v_isZero_2001_ = lean_nat_dec_eq(v_i_1999_, v_zero_2000_);
if (v_isZero_2001_ == 1)
{
lean_object* v___x_2002_; 
lean_dec(v_i_1999_);
lean_dec_ref(v_f_1998_);
lean_dec_ref(v_a_1997_);
v___x_2002_ = lean_box(0);
return v___x_2002_;
}
else
{
lean_object* v_one_2003_; lean_object* v_n_2004_; lean_object* v_v_2005_; lean_object* v___x_2006_; 
v_one_2003_ = lean_unsigned_to_nat(1u);
v_n_2004_ = lean_nat_sub(v_i_1999_, v_one_2003_);
lean_dec(v_i_1999_);
v_v_2005_ = lean_array_fget_borrowed(v_a_1997_, v_n_2004_);
lean_inc_ref(v_f_1998_);
lean_inc(v_v_2005_);
v___x_2006_ = lean_apply_1(v_f_1998_, v_v_2005_);
if (lean_obj_tag(v___x_2006_) == 0)
{
v_i_1999_ = v_n_2004_;
goto _start;
}
else
{
lean_object* v_val_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2016_; 
lean_dec_ref(v_f_1998_);
v_val_2008_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2010_ = v___x_2006_;
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_val_2008_);
lean_dec(v___x_2006_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = lean_array_fset(v_a_1997_, v_n_2004_, v_val_2008_);
lean_dec(v_n_2004_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2012_);
v___x_2014_ = v___x_2010_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object* v_00_u03b1_2017_, lean_object* v_a_2018_, lean_object* v_f_2019_, lean_object* v_i_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(v_a_2018_, v_f_2019_, v_i_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* v_info_2022_, lean_object* v_x_2023_){
_start:
{
switch(lean_obj_tag(v_x_2023_))
{
case 2:
{
lean_object* v_val_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2032_; 
v_val_2024_ = lean_ctor_get(v_x_2023_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_x_2023_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; 
v_unused_2033_ = lean_ctor_get(v_x_2023_, 0);
lean_dec(v_unused_2033_);
v___x_2026_ = v_x_2023_;
v_isShared_2027_ = v_isSharedCheck_2032_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_val_2024_);
lean_dec(v_x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2032_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v_info_2022_);
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_info_2022_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_val_2024_);
v___x_2029_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
}
case 3:
{
lean_object* v_rawVal_2034_; lean_object* v_val_2035_; lean_object* v_preresolved_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2044_; 
v_rawVal_2034_ = lean_ctor_get(v_x_2023_, 1);
v_val_2035_ = lean_ctor_get(v_x_2023_, 2);
v_preresolved_2036_ = lean_ctor_get(v_x_2023_, 3);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_x_2023_);
if (v_isSharedCheck_2044_ == 0)
{
lean_object* v_unused_2045_; 
v_unused_2045_ = lean_ctor_get(v_x_2023_, 0);
lean_dec(v_unused_2045_);
v___x_2038_ = v_x_2023_;
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_preresolved_2036_);
lean_inc(v_val_2035_);
lean_inc(v_rawVal_2034_);
lean_dec(v_x_2023_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v_info_2022_);
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_info_2022_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_rawVal_2034_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_val_2035_);
lean_ctor_set(v_reuseFailAlloc_2043_, 3, v_preresolved_2036_);
v___x_2041_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
return v___x_2042_;
}
}
}
case 1:
{
lean_object* v_info_2046_; lean_object* v_kind_2047_; lean_object* v_args_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2066_; 
v_info_2046_ = lean_ctor_get(v_x_2023_, 0);
v_kind_2047_ = lean_ctor_get(v_x_2023_, 1);
v_args_2048_ = lean_ctor_get(v_x_2023_, 2);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_x_2023_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2050_ = v_x_2023_;
v_isShared_2051_ = v_isSharedCheck_2066_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_args_2048_);
lean_inc(v_kind_2047_);
lean_inc(v_info_2046_);
lean_dec(v_x_2023_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2066_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = lean_array_get_size(v_args_2048_);
v___x_2053_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(v_info_2022_, v_args_2048_, v___x_2052_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v___x_2054_; 
lean_del_object(v___x_2050_);
lean_dec(v_kind_2047_);
lean_dec(v_info_2046_);
v___x_2054_ = lean_box(0);
return v___x_2054_;
}
else
{
lean_object* v_val_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2065_; 
v_val_2055_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2057_ = v___x_2053_;
v_isShared_2058_ = v_isSharedCheck_2065_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_val_2055_);
lean_dec(v___x_2053_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2065_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 2, v_val_2055_);
v___x_2060_ = v___x_2050_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_info_2046_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_kind_2047_);
lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_val_2055_);
v___x_2060_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2062_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v___x_2060_);
v___x_2062_ = v___x_2057_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2067_; 
lean_dec(v_x_2023_);
lean_dec(v_info_2022_);
v___x_2067_ = lean_box(0);
return v___x_2067_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object* v_info_2068_, lean_object* v_a_2069_, lean_object* v_i_2070_){
_start:
{
lean_object* v_zero_2071_; uint8_t v_isZero_2072_; 
v_zero_2071_ = lean_unsigned_to_nat(0u);
v_isZero_2072_ = lean_nat_dec_eq(v_i_2070_, v_zero_2071_);
if (v_isZero_2072_ == 1)
{
lean_object* v___x_2073_; 
lean_dec(v_i_2070_);
lean_dec_ref(v_a_2069_);
lean_dec(v_info_2068_);
v___x_2073_ = lean_box(0);
return v___x_2073_;
}
else
{
lean_object* v_one_2074_; lean_object* v_n_2075_; lean_object* v_v_2076_; lean_object* v___x_2077_; 
v_one_2074_ = lean_unsigned_to_nat(1u);
v_n_2075_ = lean_nat_sub(v_i_2070_, v_one_2074_);
lean_dec(v_i_2070_);
v_v_2076_ = lean_array_fget_borrowed(v_a_2069_, v_n_2075_);
lean_inc(v_v_2076_);
lean_inc(v_info_2068_);
v___x_2077_ = l_Lean_Syntax_setTailInfoAux(v_info_2068_, v_v_2076_);
if (lean_obj_tag(v___x_2077_) == 0)
{
v_i_2070_ = v_n_2075_;
goto _start;
}
else
{
lean_object* v_val_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v_info_2068_);
v_val_2079_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2081_ = v___x_2077_;
v_isShared_2082_ = v_isSharedCheck_2087_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_val_2079_);
lean_dec(v___x_2077_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2087_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2083_ = lean_array_fset(v_a_2069_, v_n_2075_, v_val_2079_);
lean_dec(v_n_2075_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2083_);
v___x_2085_ = v___x_2081_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object* v_stx_2088_, lean_object* v_info_2089_){
_start:
{
lean_object* v___x_2090_; 
lean_inc(v_stx_2088_);
v___x_2090_ = l_Lean_Syntax_setTailInfoAux(v_info_2089_, v_stx_2088_);
if (lean_obj_tag(v___x_2090_) == 0)
{
return v_stx_2088_;
}
else
{
lean_object* v_val_2091_; 
lean_dec(v_stx_2088_);
v_val_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_val_2091_);
lean_dec_ref_known(v___x_2090_, 1);
return v_val_2091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object* v_stx_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_Syntax_getTailInfo(v_stx_2092_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_trailing_2094_; lean_object* v_leading_2095_; lean_object* v_pos_2096_; lean_object* v_endPos_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2115_; 
v_trailing_2094_ = lean_ctor_get(v___x_2093_, 2);
v_leading_2095_ = lean_ctor_get(v___x_2093_, 0);
v_pos_2096_ = lean_ctor_get(v___x_2093_, 1);
v_endPos_2097_ = lean_ctor_get(v___x_2093_, 3);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2099_ = v___x_2093_;
v_isShared_2100_ = v_isSharedCheck_2115_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_endPos_2097_);
lean_inc(v_trailing_2094_);
lean_inc(v_pos_2096_);
lean_inc(v_leading_2095_);
lean_dec(v___x_2093_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2115_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v_str_2101_; lean_object* v_startPos_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2113_; 
v_str_2101_ = lean_ctor_get(v_trailing_2094_, 0);
v_startPos_2102_ = lean_ctor_get(v_trailing_2094_, 1);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_trailing_2094_);
if (v_isSharedCheck_2113_ == 0)
{
lean_object* v_unused_2114_; 
v_unused_2114_ = lean_ctor_get(v_trailing_2094_, 2);
lean_dec(v_unused_2114_);
v___x_2104_ = v_trailing_2094_;
v_isShared_2105_ = v_isSharedCheck_2113_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_startPos_2102_);
lean_inc(v_str_2101_);
lean_dec(v_trailing_2094_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2113_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
lean_inc(v_startPos_2102_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 2, v_startPos_2102_);
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_str_2101_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_startPos_2102_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_startPos_2102_);
v___x_2107_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2109_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 2, v___x_2107_);
v___x_2109_ = v___x_2099_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_leading_2095_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_pos_2096_);
lean_ctor_set(v_reuseFailAlloc_2111_, 2, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2111_, 3, v_endPos_2097_);
v___x_2109_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_Syntax_setTailInfo(v_stx_2092_, v___x_2109_);
return v___x_2110_;
}
}
}
}
}
else
{
lean_dec(v___x_2093_);
return v_stx_2092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object* v_a_2116_, lean_object* v_f_2117_, lean_object* v_i_2118_){
_start:
{
lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = lean_array_get_size(v_a_2116_);
v___x_2120_ = lean_nat_dec_lt(v_i_2118_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; 
lean_dec(v_i_2118_);
lean_dec_ref(v_f_2117_);
lean_dec_ref(v_a_2116_);
v___x_2121_ = lean_box(0);
return v___x_2121_;
}
else
{
lean_object* v_v_2122_; lean_object* v___x_2123_; 
v_v_2122_ = lean_array_fget_borrowed(v_a_2116_, v_i_2118_);
lean_inc_ref(v_f_2117_);
lean_inc(v_v_2122_);
v___x_2123_ = lean_apply_1(v_f_2117_, v_v_2122_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = lean_unsigned_to_nat(1u);
v___x_2125_ = lean_nat_add(v_i_2118_, v___x_2124_);
lean_dec(v_i_2118_);
v_i_2118_ = v___x_2125_;
goto _start;
}
else
{
lean_object* v_val_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2135_; 
lean_dec_ref(v_f_2117_);
v_val_2127_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2129_ = v___x_2123_;
v_isShared_2130_ = v_isSharedCheck_2135_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_val_2127_);
lean_dec(v___x_2123_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2135_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2131_ = lean_array_fset(v_a_2116_, v_i_2118_, v_val_2127_);
lean_dec(v_i_2118_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2131_);
v___x_2133_ = v___x_2129_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object* v_00_u03b1_2136_, lean_object* v_inst_2137_, lean_object* v_a_2138_, lean_object* v_f_2139_, lean_object* v_i_2140_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(v_a_2138_, v_f_2139_, v_i_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object* v_00_u03b1_2142_, lean_object* v_inst_2143_, lean_object* v_a_2144_, lean_object* v_f_2145_, lean_object* v_i_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(v_00_u03b1_2142_, v_inst_2143_, v_a_2144_, v_f_2145_, v_i_2146_);
lean_dec(v_inst_2143_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object* v_info_2148_, lean_object* v_x_2149_){
_start:
{
switch(lean_obj_tag(v_x_2149_))
{
case 2:
{
lean_object* v_val_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2158_; 
v_val_2150_ = lean_ctor_get(v_x_2149_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_x_2149_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; 
v_unused_2159_ = lean_ctor_get(v_x_2149_, 0);
lean_dec(v_unused_2159_);
v___x_2152_ = v_x_2149_;
v_isShared_2153_ = v_isSharedCheck_2158_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_val_2150_);
lean_dec(v_x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2158_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v_info_2148_);
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_info_2148_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_val_2150_);
v___x_2155_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
return v___x_2156_;
}
}
}
case 3:
{
lean_object* v_rawVal_2160_; lean_object* v_val_2161_; lean_object* v_preresolved_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2170_; 
v_rawVal_2160_ = lean_ctor_get(v_x_2149_, 1);
v_val_2161_ = lean_ctor_get(v_x_2149_, 2);
v_preresolved_2162_ = lean_ctor_get(v_x_2149_, 3);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_x_2149_);
if (v_isSharedCheck_2170_ == 0)
{
lean_object* v_unused_2171_; 
v_unused_2171_ = lean_ctor_get(v_x_2149_, 0);
lean_dec(v_unused_2171_);
v___x_2164_ = v_x_2149_;
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_preresolved_2162_);
lean_inc(v_val_2161_);
lean_inc(v_rawVal_2160_);
lean_dec(v_x_2149_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v_info_2148_);
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_info_2148_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_rawVal_2160_);
lean_ctor_set(v_reuseFailAlloc_2169_, 2, v_val_2161_);
lean_ctor_set(v_reuseFailAlloc_2169_, 3, v_preresolved_2162_);
v___x_2167_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
return v___x_2168_;
}
}
}
case 1:
{
lean_object* v_info_2172_; lean_object* v_kind_2173_; lean_object* v_args_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2192_; 
v_info_2172_ = lean_ctor_get(v_x_2149_, 0);
v_kind_2173_ = lean_ctor_get(v_x_2149_, 1);
v_args_2174_ = lean_ctor_get(v_x_2149_, 2);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_x_2149_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2176_ = v_x_2149_;
v_isShared_2177_ = v_isSharedCheck_2192_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_args_2174_);
lean_inc(v_kind_2173_);
lean_inc(v_info_2172_);
lean_dec(v_x_2149_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2192_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_unsigned_to_nat(0u);
v___x_2179_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(v_info_2148_, v_args_2174_, v___x_2178_);
if (lean_obj_tag(v___x_2179_) == 1)
{
lean_object* v_val_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2190_; 
v_val_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2190_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_val_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2190_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 2, v_val_2180_);
v___x_2185_ = v___x_2176_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_info_2172_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_kind_2173_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_val_2180_);
v___x_2185_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2187_; 
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2185_);
v___x_2187_ = v___x_2182_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_object* v___x_2191_; 
lean_dec(v___x_2179_);
lean_del_object(v___x_2176_);
lean_dec(v_kind_2173_);
lean_dec(v_info_2172_);
v___x_2191_ = lean_box(0);
return v___x_2191_;
}
}
}
default: 
{
lean_object* v___x_2193_; 
lean_dec(v_x_2149_);
lean_dec(v_info_2148_);
v___x_2193_ = lean_box(0);
return v___x_2193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object* v_info_2194_, lean_object* v_a_2195_, lean_object* v_i_2196_){
_start:
{
lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = lean_array_get_size(v_a_2195_);
v___x_2198_ = lean_nat_dec_lt(v_i_2196_, v___x_2197_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; 
lean_dec(v_i_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_info_2194_);
v___x_2199_ = lean_box(0);
return v___x_2199_;
}
else
{
lean_object* v_v_2200_; lean_object* v___x_2201_; 
v_v_2200_ = lean_array_fget_borrowed(v_a_2195_, v_i_2196_);
lean_inc(v_v_2200_);
lean_inc(v_info_2194_);
v___x_2201_ = l_Lean_Syntax_setHeadInfoAux(v_info_2194_, v_v_2200_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_unsigned_to_nat(1u);
v___x_2203_ = lean_nat_add(v_i_2196_, v___x_2202_);
lean_dec(v_i_2196_);
v_i_2196_ = v___x_2203_;
goto _start;
}
else
{
lean_object* v_val_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_info_2194_);
v_val_2205_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2207_ = v___x_2201_;
v_isShared_2208_ = v_isSharedCheck_2213_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_val_2205_);
lean_dec(v___x_2201_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2213_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2209_ = lean_array_fset(v_a_2195_, v_i_2196_, v_val_2205_);
lean_dec(v_i_2196_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2209_);
v___x_2211_ = v___x_2207_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object* v_stx_2214_, lean_object* v_info_2215_){
_start:
{
lean_object* v___x_2216_; 
lean_inc(v_stx_2214_);
v___x_2216_ = l_Lean_Syntax_setHeadInfoAux(v_info_2215_, v_stx_2214_);
if (lean_obj_tag(v___x_2216_) == 0)
{
return v_stx_2214_;
}
else
{
lean_object* v_val_2217_; 
lean_dec(v_stx_2214_);
v_val_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v___x_2216_, 1);
return v_val_2217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object* v_info_2218_, lean_object* v_x_2219_){
_start:
{
switch(lean_obj_tag(v_x_2219_))
{
case 0:
{
lean_dec(v_info_2218_);
return v_x_2219_;
}
case 1:
{
lean_object* v_kind_2220_; lean_object* v_args_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
v_kind_2220_ = lean_ctor_get(v_x_2219_, 1);
v_args_2221_ = lean_ctor_get(v_x_2219_, 2);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_x_2219_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v_x_2219_, 0);
lean_dec(v_unused_2229_);
v___x_2223_ = v_x_2219_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_args_2221_);
lean_inc(v_kind_2220_);
lean_dec(v_x_2219_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v_info_2218_);
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_info_2218_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_kind_2220_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_args_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
case 2:
{
lean_object* v_val_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
v_val_2230_ = lean_ctor_get(v_x_2219_, 1);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_x_2219_);
if (v_isSharedCheck_2237_ == 0)
{
lean_object* v_unused_2238_; 
v_unused_2238_ = lean_ctor_get(v_x_2219_, 0);
lean_dec(v_unused_2238_);
v___x_2232_ = v_x_2219_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_val_2230_);
lean_dec(v_x_2219_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v_info_2218_);
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_info_2218_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_val_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
default: 
{
lean_object* v_rawVal_2239_; lean_object* v_val_2240_; lean_object* v_preresolved_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
v_rawVal_2239_ = lean_ctor_get(v_x_2219_, 1);
v_val_2240_ = lean_ctor_get(v_x_2219_, 2);
v_preresolved_2241_ = lean_ctor_get(v_x_2219_, 3);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_x_2219_);
if (v_isSharedCheck_2248_ == 0)
{
lean_object* v_unused_2249_; 
v_unused_2249_ = lean_ctor_get(v_x_2219_, 0);
lean_dec(v_unused_2249_);
v___x_2243_ = v_x_2219_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_preresolved_2241_);
lean_inc(v_val_2240_);
lean_inc(v_rawVal_2239_);
lean_dec(v_x_2219_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v_info_2218_);
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_info_2218_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_rawVal_2239_);
lean_ctor_set(v_reuseFailAlloc_2247_, 2, v_val_2240_);
lean_ctor_set(v_reuseFailAlloc_2247_, 3, v_preresolved_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object* v_x_2253_){
_start:
{
switch(lean_obj_tag(v_x_2253_))
{
case 2:
{
lean_object* v_info_2254_; uint8_t v___x_2255_; lean_object* v___x_2256_; 
v_info_2254_ = lean_ctor_get(v_x_2253_, 0);
v___x_2255_ = 0;
v___x_2256_ = l_Lean_SourceInfo_getPos_x3f(v_info_2254_, v___x_2255_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v___x_2257_; 
lean_dec_ref_known(v_x_2253_, 2);
v___x_2257_ = lean_box(0);
return v___x_2257_;
}
else
{
lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2264_ == 0)
{
lean_object* v_unused_2265_; 
v_unused_2265_ = lean_ctor_get(v___x_2256_, 0);
lean_dec(v_unused_2265_);
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v_x_2253_);
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_x_2253_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
case 3:
{
lean_object* v_info_2266_; uint8_t v___x_2267_; lean_object* v___x_2268_; 
v_info_2266_ = lean_ctor_get(v_x_2253_, 0);
v___x_2267_ = 0;
v___x_2268_ = l_Lean_SourceInfo_getPos_x3f(v_info_2266_, v___x_2267_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v___x_2269_; 
lean_dec_ref_known(v_x_2253_, 4);
v___x_2269_ = lean_box(0);
return v___x_2269_;
}
else
{
lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2276_ == 0)
{
lean_object* v_unused_2277_; 
v_unused_2277_ = lean_ctor_get(v___x_2268_, 0);
lean_dec(v_unused_2277_);
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v_x_2253_);
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_x_2253_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
case 1:
{
lean_object* v_info_2278_; 
v_info_2278_ = lean_ctor_get(v_x_2253_, 0);
if (lean_obj_tag(v_info_2278_) == 2)
{
lean_object* v_args_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; size_t v_sz_2282_; size_t v___x_2283_; lean_object* v___x_2284_; lean_object* v_fst_2285_; 
v_args_2279_ = lean_ctor_get(v_x_2253_, 2);
lean_inc_ref(v_args_2279_);
lean_dec_ref_known(v_x_2253_, 3);
v___x_2280_ = lean_box(0);
v___x_2281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_2282_ = lean_array_size(v_args_2279_);
v___x_2283_ = ((size_t)0ULL);
v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_args_2279_, v_sz_2282_, v___x_2283_, v___x_2281_);
lean_dec_ref(v_args_2279_);
v_fst_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_fst_2285_);
lean_dec_ref(v___x_2284_);
if (lean_obj_tag(v_fst_2285_) == 0)
{
return v___x_2280_;
}
else
{
lean_object* v_val_2286_; 
v_val_2286_ = lean_ctor_get(v_fst_2285_, 0);
lean_inc(v_val_2286_);
lean_dec_ref_known(v_fst_2285_, 1);
return v_val_2286_;
}
}
else
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2287_, 0, v_x_2253_);
return v___x_2287_;
}
}
default: 
{
lean_object* v___x_2288_; 
lean_dec(v_x_2253_);
v___x_2288_ = lean_box(0);
return v___x_2288_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object* v_as_2289_, size_t v_sz_2290_, size_t v_i_2291_, lean_object* v_b_2292_){
_start:
{
uint8_t v___x_2293_; 
v___x_2293_ = lean_usize_dec_lt(v_i_2291_, v_sz_2290_);
if (v___x_2293_ == 0)
{
lean_inc_ref(v_b_2292_);
return v_b_2292_;
}
else
{
lean_object* v___x_2294_; lean_object* v_a_2295_; lean_object* v___x_2296_; 
v___x_2294_ = lean_box(0);
v_a_2295_ = lean_array_uget_borrowed(v_as_2289_, v_i_2291_);
lean_inc(v_a_2295_);
v___x_2296_ = l_Lean_Syntax_getHead_x3f(v_a_2295_);
if (lean_obj_tag(v___x_2296_) == 1)
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v___x_2294_);
return v___x_2298_;
}
else
{
lean_object* v___x_2299_; size_t v___x_2300_; size_t v___x_2301_; 
lean_dec(v___x_2296_);
v___x_2299_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_2300_ = ((size_t)1ULL);
v___x_2301_ = lean_usize_add(v_i_2291_, v___x_2300_);
v_i_2291_ = v___x_2301_;
v_b_2292_ = v___x_2299_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object* v_as_2303_, lean_object* v_sz_2304_, lean_object* v_i_2305_, lean_object* v_b_2306_){
_start:
{
size_t v_sz_boxed_2307_; size_t v_i_boxed_2308_; lean_object* v_res_2309_; 
v_sz_boxed_2307_ = lean_unbox_usize(v_sz_2304_);
lean_dec(v_sz_2304_);
v_i_boxed_2308_ = lean_unbox_usize(v_i_2305_);
lean_dec(v_i_2305_);
v_res_2309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_as_2303_, v_sz_boxed_2307_, v_i_boxed_2308_, v_b_2306_);
lean_dec_ref(v_b_2306_);
lean_dec_ref(v_as_2303_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object* v_target_2310_, lean_object* v_source_2311_){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2312_ = l_Lean_Syntax_getHeadInfo(v_source_2311_);
v___x_2313_ = l_Lean_Syntax_setHeadInfo(v_target_2310_, v___x_2312_);
v___x_2314_ = l_Lean_Syntax_getTailInfo(v_source_2311_);
v___x_2315_ = l_Lean_Syntax_setTailInfo(v___x_2313_, v___x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object* v_target_2316_, lean_object* v_source_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_target_2316_, v_source_2317_);
lean_dec(v_source_2317_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object* v_stx_2319_){
_start:
{
uint8_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = 0;
v___x_2321_ = l_Lean_SourceInfo_fromRef(v_stx_2319_, v___x_2320_);
v___x_2322_ = l_Lean_Syntax_setHeadInfo(v_stx_2319_, v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object* v_val_2323_, lean_object* v_withRef_2324_, lean_object* v_x_2325_, lean_object* v_oldRef_2326_){
_start:
{
lean_object* v_ref_2327_; lean_object* v___x_2328_; 
v_ref_2327_ = l_Lean_replaceRef(v_val_2323_, v_oldRef_2326_);
v___x_2328_ = lean_apply_3(v_withRef_2324_, lean_box(0), v_ref_2327_, v_x_2325_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object* v_val_2329_, lean_object* v_withRef_2330_, lean_object* v_x_2331_, lean_object* v_oldRef_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_withHeadRefOnly___redArg___lam__0(v_val_2329_, v_withRef_2330_, v_x_2331_, v_oldRef_2332_);
lean_dec(v_oldRef_2332_);
lean_dec(v_val_2329_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object* v_x_2334_, lean_object* v_withRef_2335_, lean_object* v_toBind_2336_, lean_object* v_getRef_2337_, lean_object* v_____do__lift_2338_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Syntax_getHead_x3f(v_____do__lift_2338_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_dec(v_getRef_2337_);
lean_dec(v_toBind_2336_);
lean_dec(v_withRef_2335_);
return v_x_2334_;
}
else
{
lean_object* v_val_2340_; lean_object* v___f_2341_; lean_object* v___x_2342_; 
v_val_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_val_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___f_2341_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2341_, 0, v_val_2340_);
lean_closure_set(v___f_2341_, 1, v_withRef_2335_);
lean_closure_set(v___f_2341_, 2, v_x_2334_);
v___x_2342_ = lean_apply_4(v_toBind_2336_, lean_box(0), lean_box(0), v_getRef_2337_, v___f_2341_);
return v___x_2342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object* v_inst_2343_, lean_object* v_inst_2344_, lean_object* v_x_2345_){
_start:
{
lean_object* v_toBind_2346_; lean_object* v_getRef_2347_; lean_object* v_withRef_2348_; lean_object* v___f_2349_; lean_object* v___x_2350_; 
v_toBind_2346_ = lean_ctor_get(v_inst_2343_, 1);
lean_inc_n(v_toBind_2346_, 2);
lean_dec_ref(v_inst_2343_);
v_getRef_2347_ = lean_ctor_get(v_inst_2344_, 0);
lean_inc_n(v_getRef_2347_, 2);
v_withRef_2348_ = lean_ctor_get(v_inst_2344_, 1);
lean_inc(v_withRef_2348_);
lean_dec_ref(v_inst_2344_);
v___f_2349_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2349_, 0, v_x_2345_);
lean_closure_set(v___f_2349_, 1, v_withRef_2348_);
lean_closure_set(v___f_2349_, 2, v_toBind_2346_);
lean_closure_set(v___f_2349_, 3, v_getRef_2347_);
v___x_2350_ = lean_apply_4(v_toBind_2346_, lean_box(0), lean_box(0), v_getRef_2347_, v___f_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object* v_m_2351_, lean_object* v_inst_2352_, lean_object* v_inst_2353_, lean_object* v_00_u03b1_2354_, lean_object* v_x_2355_){
_start:
{
lean_object* v_toBind_2356_; lean_object* v_getRef_2357_; lean_object* v_withRef_2358_; lean_object* v___f_2359_; lean_object* v___x_2360_; 
v_toBind_2356_ = lean_ctor_get(v_inst_2352_, 1);
lean_inc_n(v_toBind_2356_, 2);
lean_dec_ref(v_inst_2352_);
v_getRef_2357_ = lean_ctor_get(v_inst_2353_, 0);
lean_inc_n(v_getRef_2357_, 2);
v_withRef_2358_ = lean_ctor_get(v_inst_2353_, 1);
lean_inc(v_withRef_2358_);
lean_dec_ref(v_inst_2353_);
v___f_2359_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2359_, 0, v_x_2355_);
lean_closure_set(v___f_2359_, 1, v_withRef_2358_);
lean_closure_set(v___f_2359_, 2, v_toBind_2356_);
lean_closure_set(v___f_2359_, 3, v_getRef_2357_);
v___x_2360_ = lean_apply_4(v_toBind_2356_, lean_box(0), lean_box(0), v_getRef_2357_, v___f_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(lean_object* v_k_2370_){
_start:
{
lean_object* v___x_2371_; uint8_t v___x_2372_; uint8_t v___x_2373_; 
v___x_2371_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_2372_ = lean_name_eq(v_k_2370_, v___x_2371_);
v___x_2373_ = lean_bool_not(v___x_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object* v_k_2374_){
_start:
{
uint8_t v_res_2375_; lean_object* v_r_2376_; 
v_res_2375_ = l_Lean_expandMacros___lam__0(v_k_2374_);
lean_dec(v_k_2374_);
v_r_2376_ = lean_box(v_res_2375_);
return v_r_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object* v_stx_2379_, lean_object* v_p_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
if (lean_obj_tag(v_stx_2379_) == 1)
{
lean_object* v_info_2383_; lean_object* v_kind_2384_; lean_object* v_args_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; 
v_info_2383_ = lean_ctor_get(v_stx_2379_, 0);
v_kind_2384_ = lean_ctor_get(v_stx_2379_, 1);
v_args_2385_ = lean_ctor_get(v_stx_2379_, 2);
lean_inc(v_kind_2384_);
v___x_2386_ = lean_apply_1(v_p_2380_, v_kind_2384_);
v___x_2387_ = lean_unbox(v___x_2386_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; 
lean_dec_ref(v_a_2381_);
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v_stx_2379_);
lean_ctor_set(v___x_2388_, 1, v_a_2382_);
return v___x_2388_;
}
else
{
lean_object* v_methods_2389_; lean_object* v_quotContext_2390_; lean_object* v_currMacroScope_2391_; lean_object* v_currRecDepth_2392_; lean_object* v_maxRecDepth_2393_; lean_object* v_ref_2394_; lean_object* v_ref_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_methods_2389_ = lean_ctor_get(v_a_2381_, 0);
lean_inc_n(v_methods_2389_, 2);
v_quotContext_2390_ = lean_ctor_get(v_a_2381_, 1);
lean_inc_n(v_quotContext_2390_, 2);
v_currMacroScope_2391_ = lean_ctor_get(v_a_2381_, 2);
lean_inc_n(v_currMacroScope_2391_, 2);
v_currRecDepth_2392_ = lean_ctor_get(v_a_2381_, 3);
lean_inc_n(v_currRecDepth_2392_, 2);
v_maxRecDepth_2393_ = lean_ctor_get(v_a_2381_, 4);
lean_inc_n(v_maxRecDepth_2393_, 2);
v_ref_2394_ = lean_ctor_get(v_a_2381_, 5);
lean_inc(v_ref_2394_);
lean_dec_ref(v_a_2381_);
v_ref_2395_ = l_Lean_replaceRef(v_stx_2379_, v_ref_2394_);
lean_dec(v_ref_2394_);
lean_inc(v_ref_2395_);
v___x_2396_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2396_, 0, v_methods_2389_);
lean_ctor_set(v___x_2396_, 1, v_quotContext_2390_);
lean_ctor_set(v___x_2396_, 2, v_currMacroScope_2391_);
lean_ctor_set(v___x_2396_, 3, v_currRecDepth_2392_);
lean_ctor_set(v___x_2396_, 4, v_maxRecDepth_2393_);
lean_ctor_set(v___x_2396_, 5, v_ref_2395_);
lean_inc_ref(v_stx_2379_);
v___x_2397_ = l_Lean_Macro_expandMacro_x3f(v_stx_2379_, v___x_2396_, v_a_2382_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
if (lean_obj_tag(v_a_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2443_; 
lean_dec_ref_known(v___x_2396_, 6);
v_a_2399_ = lean_ctor_get(v___x_2397_, 1);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2443_ == 0)
{
lean_object* v_unused_2444_; 
v_unused_2444_ = lean_ctor_get(v___x_2397_, 0);
lean_dec(v_unused_2444_);
v___x_2401_ = v___x_2397_;
v_isShared_2402_ = v_isSharedCheck_2443_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2397_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2443_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
uint8_t v___x_2403_; 
v___x_2403_ = lean_nat_dec_eq(v_currRecDepth_2392_, v_maxRecDepth_2393_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2434_; 
lean_inc_ref(v_args_2385_);
lean_inc(v_kind_2384_);
lean_inc(v_info_2383_);
lean_del_object(v___x_2401_);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_stx_2379_);
if (v_isSharedCheck_2434_ == 0)
{
lean_object* v_unused_2435_; lean_object* v_unused_2436_; lean_object* v_unused_2437_; 
v_unused_2435_ = lean_ctor_get(v_stx_2379_, 2);
lean_dec(v_unused_2435_);
v_unused_2436_ = lean_ctor_get(v_stx_2379_, 1);
lean_dec(v_unused_2436_);
v_unused_2437_ = lean_ctor_get(v_stx_2379_, 0);
lean_dec(v_unused_2437_);
v___x_2405_ = v_stx_2379_;
v_isShared_2406_ = v_isSharedCheck_2434_;
goto v_resetjp_2404_;
}
else
{
lean_dec(v_stx_2379_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2434_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; size_t v_sz_2410_; size_t v___x_2411_; lean_object* v___x_2412_; 
v___x_2407_ = lean_unsigned_to_nat(1u);
v___x_2408_ = lean_nat_add(v_currRecDepth_2392_, v___x_2407_);
lean_dec(v_currRecDepth_2392_);
v___x_2409_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2409_, 0, v_methods_2389_);
lean_ctor_set(v___x_2409_, 1, v_quotContext_2390_);
lean_ctor_set(v___x_2409_, 2, v_currMacroScope_2391_);
lean_ctor_set(v___x_2409_, 3, v___x_2408_);
lean_ctor_set(v___x_2409_, 4, v_maxRecDepth_2393_);
lean_ctor_set(v___x_2409_, 5, v_ref_2395_);
v_sz_2410_ = lean_array_size(v_args_2385_);
v___x_2411_ = ((size_t)0ULL);
v___x_2412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v_sz_2410_, v___x_2411_, v_args_2385_, v___x_2409_, v_a_2399_);
lean_dec_ref_known(v___x_2409_, 6);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2424_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_a_2414_ = lean_ctor_get(v___x_2412_, 1);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2416_ = v___x_2412_;
v_isShared_2417_ = v_isSharedCheck_2424_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2424_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 2, v_a_2413_);
v___x_2419_ = v___x_2405_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_info_2383_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_kind_2384_);
lean_ctor_set(v_reuseFailAlloc_2423_, 2, v_a_2413_);
v___x_2419_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2421_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2419_);
v___x_2421_ = v___x_2416_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_a_2414_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_del_object(v___x_2405_);
lean_dec(v_kind_2384_);
lean_dec(v_info_2383_);
v_a_2425_ = lean_ctor_get(v___x_2412_, 0);
v_a_2426_ = lean_ctor_get(v___x_2412_, 1);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2412_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_inc(v_a_2425_);
lean_dec(v___x_2412_);
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
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2425_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_a_2426_);
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
}
else
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2441_; 
lean_dec(v_ref_2395_);
lean_dec(v_maxRecDepth_2393_);
lean_dec(v_currRecDepth_2392_);
lean_dec(v_currMacroScope_2391_);
lean_dec(v_quotContext_2390_);
lean_dec(v_methods_2389_);
v___x_2438_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2439_, 0, v_stx_2379_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set_tag(v___x_2401_, 1);
lean_ctor_set(v___x_2401_, 0, v___x_2439_);
v___x_2441_ = v___x_2401_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_a_2399_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
lean_object* v_a_2445_; lean_object* v_val_2446_; lean_object* v___f_2447_; 
lean_dec(v_ref_2395_);
lean_dec(v_maxRecDepth_2393_);
lean_dec(v_currRecDepth_2392_);
lean_dec(v_currMacroScope_2391_);
lean_dec(v_quotContext_2390_);
lean_dec(v_methods_2389_);
lean_dec_ref_known(v_stx_2379_, 3);
v_a_2445_ = lean_ctor_get(v___x_2397_, 1);
lean_inc(v_a_2445_);
lean_dec_ref_known(v___x_2397_, 2);
v_val_2446_ = lean_ctor_get(v_a_2398_, 0);
lean_inc(v_val_2446_);
lean_dec_ref_known(v_a_2398_, 1);
v___f_2447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___closed__0));
v_stx_2379_ = v_val_2446_;
v_p_2380_ = v___f_2447_;
v_a_2381_ = v___x_2396_;
v_a_2382_ = v_a_2445_;
goto _start;
}
}
else
{
lean_object* v_a_2449_; lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec_ref_known(v___x_2396_, 6);
lean_dec(v_ref_2395_);
lean_dec(v_maxRecDepth_2393_);
lean_dec(v_currRecDepth_2392_);
lean_dec(v_currMacroScope_2391_);
lean_dec(v_quotContext_2390_);
lean_dec(v_methods_2389_);
lean_dec_ref_known(v_stx_2379_, 3);
v_a_2449_ = lean_ctor_get(v___x_2397_, 0);
v_a_2450_ = lean_ctor_get(v___x_2397_, 1);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2397_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_inc(v_a_2449_);
lean_dec(v___x_2397_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2449_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
else
{
lean_object* v___x_2458_; 
lean_dec_ref(v_a_2381_);
lean_dec_ref(v_p_2380_);
v___x_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2458_, 0, v_stx_2379_);
lean_ctor_set(v___x_2458_, 1, v_a_2382_);
return v___x_2458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(size_t v_sz_2459_, size_t v_i_2460_, lean_object* v_bs_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
uint8_t v___x_2464_; 
v___x_2464_ = lean_usize_dec_lt(v_i_2460_, v_sz_2459_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2465_, 0, v_bs_2461_);
lean_ctor_set(v___x_2465_, 1, v___y_2463_);
return v___x_2465_;
}
else
{
lean_object* v___f_2466_; lean_object* v_v_2467_; lean_object* v___x_2468_; 
v___f_2466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___closed__0));
v_v_2467_ = lean_array_uget_borrowed(v_bs_2461_, v_i_2460_);
lean_inc_ref(v___y_2462_);
lean_inc(v_v_2467_);
v___x_2468_ = l_Lean_expandMacros(v_v_2467_, v___f_2466_, v___y_2462_, v___y_2463_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v_a_2470_; lean_object* v___x_2471_; lean_object* v_bs_x27_2472_; size_t v___x_2473_; size_t v___x_2474_; lean_object* v___x_2475_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
v_a_2470_ = lean_ctor_get(v___x_2468_, 1);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2468_, 2);
v___x_2471_ = lean_unsigned_to_nat(0u);
v_bs_x27_2472_ = lean_array_uset(v_bs_2461_, v_i_2460_, v___x_2471_);
v___x_2473_ = ((size_t)1ULL);
v___x_2474_ = lean_usize_add(v_i_2460_, v___x_2473_);
v___x_2475_ = lean_array_uset(v_bs_x27_2472_, v_i_2460_, v_a_2469_);
v_i_2460_ = v___x_2474_;
v_bs_2461_ = v___x_2475_;
v___y_2463_ = v_a_2470_;
goto _start;
}
else
{
lean_object* v_a_2477_; lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec_ref(v_bs_2461_);
v_a_2477_ = lean_ctor_get(v___x_2468_, 0);
v_a_2478_ = lean_ctor_get(v___x_2468_, 1);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2468_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_inc(v_a_2477_);
lean_dec(v___x_2468_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2477_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object* v_sz_2486_, lean_object* v_i_2487_, lean_object* v_bs_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
size_t v_sz_boxed_2491_; size_t v_i_boxed_2492_; lean_object* v_res_2493_; 
v_sz_boxed_2491_ = lean_unbox_usize(v_sz_2486_);
lean_dec(v_sz_2486_);
v_i_boxed_2492_ = lean_unbox_usize(v_i_2487_);
lean_dec(v_i_2487_);
v_res_2493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v_sz_boxed_2491_, v_i_boxed_2492_, v_bs_2488_, v___y_2489_, v___y_2490_);
lean_dec_ref(v___y_2489_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object* v_src_2494_, lean_object* v_val_2495_, uint8_t v_canonical_2496_){
_start:
{
lean_object* v___x_2497_; uint8_t v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2497_ = l_Lean_SourceInfo_fromRef(v_src_2494_, v_canonical_2496_);
v___x_2498_ = 1;
lean_inc(v_val_2495_);
v___x_2499_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2495_, v___x_2498_);
v___x_2500_ = lean_unsigned_to_nat(0u);
v___x_2501_ = lean_string_utf8_byte_size(v___x_2499_);
v___x_2502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2499_);
lean_ctor_set(v___x_2502_, 1, v___x_2500_);
lean_ctor_set(v___x_2502_, 2, v___x_2501_);
v___x_2503_ = lean_box(0);
v___x_2504_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2497_);
lean_ctor_set(v___x_2504_, 1, v___x_2502_);
lean_ctor_set(v___x_2504_, 2, v_val_2495_);
lean_ctor_set(v___x_2504_, 3, v___x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object* v_src_2505_, lean_object* v_val_2506_, lean_object* v_canonical_2507_){
_start:
{
uint8_t v_canonical_boxed_2508_; lean_object* v_res_2509_; 
v_canonical_boxed_2508_ = lean_unbox(v_canonical_2507_);
v_res_2509_ = l_Lean_mkIdentFrom(v_src_2505_, v_val_2506_, v_canonical_boxed_2508_);
lean_dec(v_src_2505_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object* v_val_2510_, uint8_t v_canonical_2511_, lean_object* v_toPure_2512_, lean_object* v_____do__lift_2513_){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = l_Lean_mkIdentFrom(v_____do__lift_2513_, v_val_2510_, v_canonical_2511_);
v___x_2515_ = lean_apply_2(v_toPure_2512_, lean_box(0), v___x_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object* v_val_2516_, lean_object* v_canonical_2517_, lean_object* v_toPure_2518_, lean_object* v_____do__lift_2519_){
_start:
{
uint8_t v_canonical_boxed_2520_; lean_object* v_res_2521_; 
v_canonical_boxed_2520_ = lean_unbox(v_canonical_2517_);
v_res_2521_ = l_Lean_mkIdentFromRef___redArg___lam__0(v_val_2516_, v_canonical_boxed_2520_, v_toPure_2518_, v_____do__lift_2519_);
lean_dec(v_____do__lift_2519_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object* v_inst_2522_, lean_object* v_inst_2523_, lean_object* v_val_2524_, uint8_t v_canonical_2525_){
_start:
{
lean_object* v_toApplicative_2526_; lean_object* v_toBind_2527_; lean_object* v_getRef_2528_; lean_object* v_toPure_2529_; lean_object* v___x_2530_; lean_object* v___f_2531_; lean_object* v___x_2532_; 
v_toApplicative_2526_ = lean_ctor_get(v_inst_2522_, 0);
lean_inc_ref(v_toApplicative_2526_);
v_toBind_2527_ = lean_ctor_get(v_inst_2522_, 1);
lean_inc(v_toBind_2527_);
lean_dec_ref(v_inst_2522_);
v_getRef_2528_ = lean_ctor_get(v_inst_2523_, 0);
lean_inc(v_getRef_2528_);
lean_dec_ref(v_inst_2523_);
v_toPure_2529_ = lean_ctor_get(v_toApplicative_2526_, 1);
lean_inc(v_toPure_2529_);
lean_dec_ref(v_toApplicative_2526_);
v___x_2530_ = lean_box(v_canonical_2525_);
v___f_2531_ = lean_alloc_closure((void*)(l_Lean_mkIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2531_, 0, v_val_2524_);
lean_closure_set(v___f_2531_, 1, v___x_2530_);
lean_closure_set(v___f_2531_, 2, v_toPure_2529_);
v___x_2532_ = lean_apply_4(v_toBind_2527_, lean_box(0), lean_box(0), v_getRef_2528_, v___f_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object* v_inst_2533_, lean_object* v_inst_2534_, lean_object* v_val_2535_, lean_object* v_canonical_2536_){
_start:
{
uint8_t v_canonical_boxed_2537_; lean_object* v_res_2538_; 
v_canonical_boxed_2537_ = lean_unbox(v_canonical_2536_);
v_res_2538_ = l_Lean_mkIdentFromRef___redArg(v_inst_2533_, v_inst_2534_, v_val_2535_, v_canonical_boxed_2537_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object* v_m_2539_, lean_object* v_inst_2540_, lean_object* v_inst_2541_, lean_object* v_val_2542_, uint8_t v_canonical_2543_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = l_Lean_mkIdentFromRef___redArg(v_inst_2540_, v_inst_2541_, v_val_2542_, v_canonical_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object* v_m_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_val_2548_, lean_object* v_canonical_2549_){
_start:
{
uint8_t v_canonical_boxed_2550_; lean_object* v_res_2551_; 
v_canonical_boxed_2550_ = lean_unbox(v_canonical_2549_);
v_res_2551_ = l_Lean_mkIdentFromRef(v_m_2545_, v_inst_2546_, v_inst_2547_, v_val_2548_, v_canonical_boxed_2550_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object* v_src_2555_, lean_object* v_c_2556_, uint8_t v_canonical_2557_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v_id_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2558_ = ((lean_object*)(l_Lean_mkCIdentFrom___closed__1));
v___x_2559_ = lean_unsigned_to_nat(0u);
lean_inc(v_c_2556_);
v_id_2560_ = l_Lean_addMacroScope(v___x_2558_, v_c_2556_, v___x_2559_);
v___x_2561_ = l_Lean_SourceInfo_fromRef(v_src_2555_, v_canonical_2557_);
v___x_2562_ = 1;
lean_inc(v_id_2560_);
v___x_2563_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_id_2560_, v___x_2562_);
v___x_2564_ = lean_string_utf8_byte_size(v___x_2563_);
v___x_2565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2563_);
lean_ctor_set(v___x_2565_, 1, v___x_2559_);
lean_ctor_set(v___x_2565_, 2, v___x_2564_);
v___x_2566_ = lean_box(0);
v___x_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2567_, 0, v_c_2556_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v___x_2566_);
v___x_2569_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2561_);
lean_ctor_set(v___x_2569_, 1, v___x_2565_);
lean_ctor_set(v___x_2569_, 2, v_id_2560_);
lean_ctor_set(v___x_2569_, 3, v___x_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* v_src_2570_, lean_object* v_c_2571_, lean_object* v_canonical_2572_){
_start:
{
uint8_t v_canonical_boxed_2573_; lean_object* v_res_2574_; 
v_canonical_boxed_2573_ = lean_unbox(v_canonical_2572_);
v_res_2574_ = l_Lean_mkCIdentFrom(v_src_2570_, v_c_2571_, v_canonical_boxed_2573_);
lean_dec(v_src_2570_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object* v_c_2575_, uint8_t v_canonical_2576_, lean_object* v_toPure_2577_, lean_object* v_____do__lift_2578_){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = l_Lean_mkCIdentFrom(v_____do__lift_2578_, v_c_2575_, v_canonical_2576_);
v___x_2580_ = lean_apply_2(v_toPure_2577_, lean_box(0), v___x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object* v_c_2581_, lean_object* v_canonical_2582_, lean_object* v_toPure_2583_, lean_object* v_____do__lift_2584_){
_start:
{
uint8_t v_canonical_boxed_2585_; lean_object* v_res_2586_; 
v_canonical_boxed_2585_ = lean_unbox(v_canonical_2582_);
v_res_2586_ = l_Lean_mkCIdentFromRef___redArg___lam__0(v_c_2581_, v_canonical_boxed_2585_, v_toPure_2583_, v_____do__lift_2584_);
lean_dec(v_____do__lift_2584_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object* v_inst_2587_, lean_object* v_inst_2588_, lean_object* v_c_2589_, uint8_t v_canonical_2590_){
_start:
{
lean_object* v_toApplicative_2591_; lean_object* v_toBind_2592_; lean_object* v_getRef_2593_; lean_object* v_toPure_2594_; lean_object* v___x_2595_; lean_object* v___f_2596_; lean_object* v___x_2597_; 
v_toApplicative_2591_ = lean_ctor_get(v_inst_2587_, 0);
lean_inc_ref(v_toApplicative_2591_);
v_toBind_2592_ = lean_ctor_get(v_inst_2587_, 1);
lean_inc(v_toBind_2592_);
lean_dec_ref(v_inst_2587_);
v_getRef_2593_ = lean_ctor_get(v_inst_2588_, 0);
lean_inc(v_getRef_2593_);
lean_dec_ref(v_inst_2588_);
v_toPure_2594_ = lean_ctor_get(v_toApplicative_2591_, 1);
lean_inc(v_toPure_2594_);
lean_dec_ref(v_toApplicative_2591_);
v___x_2595_ = lean_box(v_canonical_2590_);
v___f_2596_ = lean_alloc_closure((void*)(l_Lean_mkCIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2596_, 0, v_c_2589_);
lean_closure_set(v___f_2596_, 1, v___x_2595_);
lean_closure_set(v___f_2596_, 2, v_toPure_2594_);
v___x_2597_ = lean_apply_4(v_toBind_2592_, lean_box(0), lean_box(0), v_getRef_2593_, v___f_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object* v_inst_2598_, lean_object* v_inst_2599_, lean_object* v_c_2600_, lean_object* v_canonical_2601_){
_start:
{
uint8_t v_canonical_boxed_2602_; lean_object* v_res_2603_; 
v_canonical_boxed_2602_ = lean_unbox(v_canonical_2601_);
v_res_2603_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2598_, v_inst_2599_, v_c_2600_, v_canonical_boxed_2602_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object* v_m_2604_, lean_object* v_inst_2605_, lean_object* v_inst_2606_, lean_object* v_c_2607_, uint8_t v_canonical_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2605_, v_inst_2606_, v_c_2607_, v_canonical_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object* v_m_2610_, lean_object* v_inst_2611_, lean_object* v_inst_2612_, lean_object* v_c_2613_, lean_object* v_canonical_2614_){
_start:
{
uint8_t v_canonical_boxed_2615_; lean_object* v_res_2616_; 
v_canonical_boxed_2615_ = lean_unbox(v_canonical_2614_);
v_res_2616_ = l_Lean_mkCIdentFromRef(v_m_2610_, v_inst_2611_, v_inst_2612_, v_c_2613_, v_canonical_boxed_2615_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object* v_c_2617_){
_start:
{
lean_object* v___x_2618_; uint8_t v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_box(0);
v___x_2619_ = 0;
v___x_2620_ = l_Lean_mkCIdentFrom(v___x_2618_, v_c_2617_, v___x_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdent(lean_object* v_val_2621_){
_start:
{
lean_object* v___x_2622_; uint8_t v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2622_ = lean_box(2);
v___x_2623_ = 1;
lean_inc(v_val_2621_);
v___x_2624_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2621_, v___x_2623_);
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = lean_string_utf8_byte_size(v___x_2624_);
v___x_2627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2624_);
lean_ctor_set(v___x_2627_, 1, v___x_2625_);
lean_ctor_set(v___x_2627_, 2, v___x_2626_);
v___x_2628_ = lean_box(0);
v___x_2629_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2622_);
lean_ctor_set(v___x_2629_, 1, v___x_2627_);
lean_ctor_set(v___x_2629_, 2, v_val_2621_);
lean_ctor_set(v___x_2629_, 3, v___x_2628_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object* v_args_2633_){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = ((lean_object*)(l_Lean_mkGroupNode___closed__1));
v___x_2635_ = lean_box(2);
v___x_2636_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
lean_ctor_set(v___x_2636_, 1, v___x_2634_);
lean_ctor_set(v___x_2636_, 2, v_args_2633_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object* v_sep_2637_, lean_object* v_as_2638_, size_t v_sz_2639_, size_t v_i_2640_, lean_object* v_b_2641_){
_start:
{
uint8_t v___x_2642_; 
v___x_2642_ = lean_usize_dec_lt(v_i_2640_, v_sz_2639_);
if (v___x_2642_ == 0)
{
lean_dec(v_sep_2637_);
return v_b_2641_;
}
else
{
lean_object* v_fst_2643_; lean_object* v_snd_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2664_; 
v_fst_2643_ = lean_ctor_get(v_b_2641_, 0);
v_snd_2644_ = lean_ctor_get(v_b_2641_, 1);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_b_2641_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2646_ = v_b_2641_;
v_isShared_2647_ = v_isSharedCheck_2664_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_snd_2644_);
lean_inc(v_fst_2643_);
lean_dec(v_b_2641_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2664_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v_r_2649_; lean_object* v_i_2658_; lean_object* v_a_2659_; uint8_t v___x_2660_; 
v_i_2658_ = lean_unsigned_to_nat(0u);
v_a_2659_ = lean_array_uget_borrowed(v_as_2638_, v_i_2640_);
v___x_2660_ = lean_nat_dec_lt(v_i_2658_, v_fst_2643_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2661_; 
lean_inc(v_a_2659_);
v___x_2661_ = lean_array_push(v_snd_2644_, v_a_2659_);
v_r_2649_ = v___x_2661_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
lean_inc(v_sep_2637_);
v___x_2662_ = lean_array_push(v_snd_2644_, v_sep_2637_);
lean_inc(v_a_2659_);
v___x_2663_ = lean_array_push(v___x_2662_, v_a_2659_);
v_r_2649_ = v___x_2663_;
goto v___jp_2648_;
}
v___jp_2648_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2650_ = lean_unsigned_to_nat(1u);
v___x_2651_ = lean_nat_add(v_fst_2643_, v___x_2650_);
lean_dec(v_fst_2643_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 1, v_r_2649_);
lean_ctor_set(v___x_2646_, 0, v___x_2651_);
v___x_2653_ = v___x_2646_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_r_2649_);
v___x_2653_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
size_t v___x_2654_; size_t v___x_2655_; 
v___x_2654_ = ((size_t)1ULL);
v___x_2655_ = lean_usize_add(v_i_2640_, v___x_2654_);
v_i_2640_ = v___x_2655_;
v_b_2641_ = v___x_2653_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object* v_sep_2665_, lean_object* v_as_2666_, lean_object* v_sz_2667_, lean_object* v_i_2668_, lean_object* v_b_2669_){
_start:
{
size_t v_sz_boxed_2670_; size_t v_i_boxed_2671_; lean_object* v_res_2672_; 
v_sz_boxed_2670_ = lean_unbox_usize(v_sz_2667_);
lean_dec(v_sz_2667_);
v_i_boxed_2671_ = lean_unbox_usize(v_i_2668_);
lean_dec(v_i_2668_);
v_res_2672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2665_, v_as_2666_, v_sz_boxed_2670_, v_i_boxed_2671_, v_b_2669_);
lean_dec_ref(v_as_2666_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object* v_as_2678_, lean_object* v_sep_2679_){
_start:
{
lean_object* v___x_2680_; size_t v_sz_2681_; size_t v___x_2682_; lean_object* v___x_2683_; lean_object* v_snd_2684_; 
v___x_2680_ = ((lean_object*)(l_Lean_mkSepArray___closed__1));
v_sz_2681_ = lean_array_size(v_as_2678_);
v___x_2682_ = ((size_t)0ULL);
v___x_2683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2679_, v_as_2678_, v_sz_2681_, v___x_2682_, v___x_2680_);
v_snd_2684_ = lean_ctor_get(v___x_2683_, 1);
lean_inc(v_snd_2684_);
lean_dec_ref(v___x_2683_);
return v_snd_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object* v_as_2685_, lean_object* v_sep_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_mkSepArray(v_as_2685_, v_sep_2686_);
lean_dec_ref(v_as_2685_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object* v_arg_2695_){
_start:
{
if (lean_obj_tag(v_arg_2695_) == 0)
{
lean_object* v___x_2696_; 
v___x_2696_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
return v___x_2696_;
}
else
{
lean_object* v_val_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v_val_2697_ = lean_ctor_get(v_arg_2695_, 0);
lean_inc(v_val_2697_);
lean_dec_ref_known(v_arg_2695_, 1);
v___x_2698_ = lean_unsigned_to_nat(1u);
v___x_2699_ = lean_mk_empty_array_with_capacity(v___x_2698_);
v___x_2700_ = lean_array_push(v___x_2699_, v_val_2697_);
v___x_2701_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2702_ = lean_box(2);
v___x_2703_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
lean_ctor_set(v___x_2703_, 1, v___x_2701_);
lean_ctor_set(v___x_2703_, 2, v___x_2700_);
return v___x_2703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object* v_ref_2710_, uint8_t v_canonical_2711_){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2712_ = ((lean_object*)(l_Lean_mkHole___closed__1));
v___x_2713_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_2714_ = l_Lean_mkAtomFrom(v_ref_2710_, v___x_2713_, v_canonical_2711_);
v___x_2715_ = lean_unsigned_to_nat(1u);
v___x_2716_ = lean_mk_empty_array_with_capacity(v___x_2715_);
v___x_2717_ = lean_array_push(v___x_2716_, v___x_2714_);
v___x_2718_ = lean_box(2);
v___x_2719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v___x_2712_);
lean_ctor_set(v___x_2719_, 2, v___x_2717_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object* v_ref_2720_, lean_object* v_canonical_2721_){
_start:
{
uint8_t v_canonical_boxed_2722_; lean_object* v_res_2723_; 
v_canonical_boxed_2722_ = lean_unbox(v_canonical_2721_);
v_res_2723_ = l_Lean_mkHole(v_ref_2720_, v_canonical_boxed_2722_);
lean_dec(v_ref_2720_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object* v_a_2724_, lean_object* v_sep_2725_){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2726_ = l_Lean_mkSepArray(v_a_2724_, v_sep_2725_);
v___x_2727_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2728_ = lean_box(2);
v___x_2729_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
lean_ctor_set(v___x_2729_, 1, v___x_2727_);
lean_ctor_set(v___x_2729_, 2, v___x_2726_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object* v_a_2730_, lean_object* v_sep_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_Syntax_mkSep(v_a_2730_, v_sep_2731_);
lean_dec_ref(v_a_2730_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object* v_sep_2739_, lean_object* v_elems_2740_){
_start:
{
uint8_t v___x_2741_; 
lean_inc_ref(v_sep_2739_);
v___x_2741_ = lean_string_isempty(v_sep_2739_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = l_Lean_mkAtom(v_sep_2739_);
v___x_2743_ = l_Lean_mkSepArray(v_elems_2740_, v___x_2742_);
return v___x_2743_;
}
else
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_dec_ref(v_sep_2739_);
v___x_2744_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___x_2745_ = l_Lean_mkSepArray(v_elems_2740_, v___x_2744_);
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object* v_sep_2746_, lean_object* v_elems_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2746_, v_elems_2747_);
lean_dec_ref(v_elems_2747_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object* v_elems_2749_, lean_object* v_toPure_2750_, lean_object* v_sep_2751_, lean_object* v_ref_2752_){
_start:
{
lean_object* v___y_2754_; uint8_t v___x_2757_; 
lean_inc_ref(v_sep_2751_);
v___x_2757_ = lean_string_isempty(v_sep_2751_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_mkAtomFrom(v_ref_2752_, v_sep_2751_, v___x_2757_);
v___y_2754_ = v___x_2758_;
goto v___jp_2753_;
}
else
{
lean_object* v___x_2759_; 
lean_dec_ref(v_sep_2751_);
v___x_2759_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___y_2754_ = v___x_2759_;
goto v___jp_2753_;
}
v___jp_2753_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = l_Lean_mkSepArray(v_elems_2749_, v___y_2754_);
v___x_2756_ = lean_apply_2(v_toPure_2750_, lean_box(0), v___x_2755_);
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object* v_elems_2760_, lean_object* v_toPure_2761_, lean_object* v_sep_2762_, lean_object* v_ref_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(v_elems_2760_, v_toPure_2761_, v_sep_2762_, v_ref_2763_);
lean_dec(v_ref_2763_);
lean_dec_ref(v_elems_2760_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object* v_inst_2765_, lean_object* v_inst_2766_, lean_object* v_sep_2767_, lean_object* v_elems_2768_){
_start:
{
lean_object* v_toApplicative_2769_; lean_object* v_toBind_2770_; lean_object* v_getRef_2771_; lean_object* v_toPure_2772_; lean_object* v___f_2773_; lean_object* v___x_2774_; 
v_toApplicative_2769_ = lean_ctor_get(v_inst_2765_, 0);
lean_inc_ref(v_toApplicative_2769_);
v_toBind_2770_ = lean_ctor_get(v_inst_2765_, 1);
lean_inc(v_toBind_2770_);
lean_dec_ref(v_inst_2765_);
v_getRef_2771_ = lean_ctor_get(v_inst_2766_, 0);
lean_inc(v_getRef_2771_);
lean_dec_ref(v_inst_2766_);
v_toPure_2772_ = lean_ctor_get(v_toApplicative_2769_, 1);
lean_inc(v_toPure_2772_);
lean_dec_ref(v_toApplicative_2769_);
v___f_2773_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2773_, 0, v_elems_2768_);
lean_closure_set(v___f_2773_, 1, v_toPure_2772_);
lean_closure_set(v___f_2773_, 2, v_sep_2767_);
v___x_2774_ = lean_apply_4(v_toBind_2770_, lean_box(0), lean_box(0), v_getRef_2771_, v___f_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object* v_m_2775_, lean_object* v_inst_2776_, lean_object* v_inst_2777_, lean_object* v_sep_2778_, lean_object* v_elems_2779_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(v_inst_2776_, v_inst_2777_, v_sep_2778_, v_elems_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeArraySepArray(lean_object* v_sep_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElems___boxed), 2, 1);
lean_closure_set(v___x_2782_, 0, v_sep_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* v_sep_2783_, lean_object* v_elems_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2783_, v_elems_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* v_sep_2786_, lean_object* v_elems_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_Syntax_TSepArray_ofElems___redArg(v_sep_2786_, v_elems_2787_);
lean_dec_ref(v_elems_2787_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* v_k_2789_, lean_object* v_sep_2790_, lean_object* v_elems_2791_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2790_, v_elems_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* v_k_2793_, lean_object* v_sep_2794_, lean_object* v_elems_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_Syntax_TSepArray_ofElems(v_k_2793_, v_sep_2794_, v_elems_2795_);
lean_dec_ref(v_elems_2795_);
lean_dec(v_k_2793_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* v_k_2797_, lean_object* v_sep_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(v___x_2799_, 0, v_k_2797_);
lean_closure_set(v___x_2799_, 1, v_sep_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* v_fn_2806_, lean_object* v_x_2807_){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
v___x_2808_ = lean_array_get_size(v_x_2807_);
v___x_2809_ = lean_unsigned_to_nat(0u);
v___x_2810_ = lean_nat_dec_eq(v___x_2808_, v___x_2809_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2811_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_2812_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2813_ = lean_box(2);
v___x_2814_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
lean_ctor_set(v___x_2814_, 1, v___x_2812_);
lean_ctor_set(v___x_2814_, 2, v_x_2807_);
v___x_2815_ = lean_unsigned_to_nat(2u);
v___x_2816_ = lean_mk_empty_array_with_capacity(v___x_2815_);
v___x_2817_ = lean_array_push(v___x_2816_, v_fn_2806_);
v___x_2818_ = lean_array_push(v___x_2817_, v___x_2814_);
v___x_2819_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2813_);
lean_ctor_set(v___x_2819_, 1, v___x_2811_);
lean_ctor_set(v___x_2819_, 2, v___x_2818_);
return v___x_2819_;
}
else
{
lean_dec_ref(v_x_2807_);
return v_fn_2806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* v_fn_2820_, lean_object* v_args_2821_){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = l_Lean_mkCIdent(v_fn_2820_);
v___x_2823_ = l_Lean_Syntax_mkApp(v___x_2822_, v_args_2821_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* v_kind_2824_, lean_object* v_val_2825_, lean_object* v_info_2826_){
_start:
{
lean_object* v_atom_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_atom_2827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2827_, 0, v_info_2826_);
lean_ctor_set(v_atom_2827_, 1, v_val_2825_);
v___x_2828_ = lean_unsigned_to_nat(1u);
v___x_2829_ = lean_mk_empty_array_with_capacity(v___x_2828_);
v___x_2830_ = lean_array_push(v___x_2829_, v_atom_2827_);
v___x_2831_ = lean_box(2);
v___x_2832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
lean_ctor_set(v___x_2832_, 1, v_kind_2824_);
lean_ctor_set(v___x_2832_, 2, v___x_2830_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t v_val_2836_, lean_object* v_info_2837_){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2838_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_2839_ = l_Char_quote(v_val_2836_);
v___x_2840_ = l_Lean_Syntax_mkLit(v___x_2838_, v___x_2839_, v_info_2837_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* v_val_2841_, lean_object* v_info_2842_){
_start:
{
uint32_t v_val_boxed_2843_; lean_object* v_res_2844_; 
v_val_boxed_2843_ = lean_unbox_uint32(v_val_2841_);
lean_dec(v_val_2841_);
v_res_2844_ = l_Lean_Syntax_mkCharLit(v_val_boxed_2843_, v_info_2842_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* v_val_2848_, lean_object* v_info_2849_){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_2851_ = l_String_quote(v_val_2848_);
v___x_2852_ = l_Lean_Syntax_mkLit(v___x_2850_, v___x_2851_, v_info_2849_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* v_val_2856_, lean_object* v_info_2857_){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2859_ = l_Lean_Syntax_mkLit(v___x_2858_, v_val_2856_, v_info_2857_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* v_val_2860_, lean_object* v_info_2861_){
_start:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2862_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2863_ = l_Nat_reprFast(v_val_2860_);
v___x_2864_ = l_Lean_Syntax_mkLit(v___x_2862_, v___x_2863_, v_info_2861_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* v_val_2868_, lean_object* v_info_2869_){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_2871_ = l_Lean_Syntax_mkLit(v___x_2870_, v_val_2868_, v_info_2869_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* v_val_2875_, lean_object* v_info_2876_){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_2878_ = l_Lean_Syntax_mkLit(v___x_2877_, v_val_2875_, v_info_2876_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* v_s_2879_, lean_object* v_i_2880_, lean_object* v_val_2881_){
_start:
{
uint8_t v___x_2882_; 
v___x_2882_ = lean_string_utf8_at_end(v_s_2879_, v_i_2880_);
if (v___x_2882_ == 0)
{
uint32_t v_c_2883_; uint32_t v___x_2884_; uint8_t v___x_2885_; 
v_c_2883_ = lean_string_utf8_get(v_s_2879_, v_i_2880_);
v___x_2884_ = 48;
v___x_2885_ = lean_uint32_dec_eq(v_c_2883_, v___x_2884_);
if (v___x_2885_ == 0)
{
uint32_t v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = 49;
v___x_2887_ = lean_uint32_dec_eq(v_c_2883_, v___x_2886_);
if (v___x_2887_ == 0)
{
uint32_t v___x_2888_; uint8_t v___x_2889_; 
v___x_2888_ = 95;
v___x_2889_ = lean_uint32_dec_eq(v_c_2883_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; 
lean_dec(v_val_2881_);
lean_dec(v_i_2880_);
v___x_2890_ = lean_box(0);
return v___x_2890_;
}
else
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_string_utf8_next(v_s_2879_, v_i_2880_);
lean_dec(v_i_2880_);
v_i_2880_ = v___x_2891_;
goto _start;
}
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2893_ = lean_string_utf8_next(v_s_2879_, v_i_2880_);
lean_dec(v_i_2880_);
v___x_2894_ = lean_unsigned_to_nat(2u);
v___x_2895_ = lean_nat_mul(v___x_2894_, v_val_2881_);
lean_dec(v_val_2881_);
v___x_2896_ = lean_unsigned_to_nat(1u);
v___x_2897_ = lean_nat_add(v___x_2895_, v___x_2896_);
lean_dec(v___x_2895_);
v_i_2880_ = v___x_2893_;
v_val_2881_ = v___x_2897_;
goto _start;
}
}
else
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = lean_string_utf8_next(v_s_2879_, v_i_2880_);
lean_dec(v_i_2880_);
v___x_2900_ = lean_unsigned_to_nat(2u);
v___x_2901_ = lean_nat_mul(v___x_2900_, v_val_2881_);
lean_dec(v_val_2881_);
v_i_2880_ = v___x_2899_;
v_val_2881_ = v___x_2901_;
goto _start;
}
}
else
{
lean_object* v___x_2903_; 
lean_dec(v_i_2880_);
v___x_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2903_, 0, v_val_2881_);
return v___x_2903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* v_s_2904_, lean_object* v_i_2905_, lean_object* v_val_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2904_, v_i_2905_, v_val_2906_);
lean_dec_ref(v_s_2904_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* v_s_2908_, lean_object* v_i_2909_, lean_object* v_val_2910_){
_start:
{
uint8_t v___x_2911_; 
v___x_2911_ = lean_string_utf8_at_end(v_s_2908_, v_i_2909_);
if (v___x_2911_ == 0)
{
uint32_t v_c_2912_; uint8_t v___y_2914_; uint32_t v___x_2928_; uint8_t v___x_2929_; 
v_c_2912_ = lean_string_utf8_get(v_s_2908_, v_i_2909_);
v___x_2928_ = 48;
v___x_2929_ = lean_uint32_dec_le(v___x_2928_, v_c_2912_);
if (v___x_2929_ == 0)
{
v___y_2914_ = v___x_2929_;
goto v___jp_2913_;
}
else
{
uint32_t v___x_2930_; uint8_t v___x_2931_; 
v___x_2930_ = 55;
v___x_2931_ = lean_uint32_dec_le(v_c_2912_, v___x_2930_);
v___y_2914_ = v___x_2931_;
goto v___jp_2913_;
}
v___jp_2913_:
{
if (v___y_2914_ == 0)
{
uint32_t v___x_2915_; uint8_t v___x_2916_; 
v___x_2915_ = 95;
v___x_2916_ = lean_uint32_dec_eq(v_c_2912_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; 
lean_dec(v_val_2910_);
lean_dec(v_i_2909_);
v___x_2917_ = lean_box(0);
return v___x_2917_;
}
else
{
lean_object* v___x_2918_; 
v___x_2918_ = lean_string_utf8_next(v_s_2908_, v_i_2909_);
lean_dec(v_i_2909_);
v_i_2909_ = v___x_2918_;
goto _start;
}
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2920_ = lean_string_utf8_next(v_s_2908_, v_i_2909_);
lean_dec(v_i_2909_);
v___x_2921_ = lean_unsigned_to_nat(8u);
v___x_2922_ = lean_nat_mul(v___x_2921_, v_val_2910_);
lean_dec(v_val_2910_);
v___x_2923_ = lean_uint32_to_nat(v_c_2912_);
v___x_2924_ = lean_nat_add(v___x_2922_, v___x_2923_);
lean_dec(v___x_2923_);
lean_dec(v___x_2922_);
v___x_2925_ = lean_unsigned_to_nat(48u);
v___x_2926_ = lean_nat_sub(v___x_2924_, v___x_2925_);
lean_dec(v___x_2924_);
v_i_2909_ = v___x_2920_;
v_val_2910_ = v___x_2926_;
goto _start;
}
}
}
else
{
lean_object* v___x_2932_; 
lean_dec(v_i_2909_);
v___x_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2932_, 0, v_val_2910_);
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* v_s_2933_, lean_object* v_i_2934_, lean_object* v_val_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2933_, v_i_2934_, v_val_2935_);
lean_dec_ref(v_s_2933_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object* v_s_2937_, lean_object* v_i_2938_){
_start:
{
uint32_t v_c_2939_; lean_object* v_i_2940_; uint8_t v___y_2942_; uint8_t v___y_2952_; uint8_t v___y_2965_; uint32_t v___x_2975_; uint8_t v___x_2976_; 
v_c_2939_ = lean_string_utf8_get(v_s_2937_, v_i_2938_);
v_i_2940_ = lean_string_utf8_next(v_s_2937_, v_i_2938_);
v___x_2975_ = 48;
v___x_2976_ = lean_uint32_dec_le(v___x_2975_, v_c_2939_);
if (v___x_2976_ == 0)
{
v___y_2965_ = v___x_2976_;
goto v___jp_2964_;
}
else
{
uint32_t v___x_2977_; uint8_t v___x_2978_; 
v___x_2977_ = 57;
v___x_2978_ = lean_uint32_dec_le(v_c_2939_, v___x_2977_);
v___y_2965_ = v___x_2978_;
goto v___jp_2964_;
}
v___jp_2941_:
{
if (v___y_2942_ == 0)
{
lean_object* v___x_2943_; 
lean_dec(v_i_2940_);
v___x_2943_ = lean_box(0);
return v___x_2943_;
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2944_ = lean_unsigned_to_nat(10u);
v___x_2945_ = lean_uint32_to_nat(v_c_2939_);
v___x_2946_ = lean_nat_add(v___x_2944_, v___x_2945_);
lean_dec(v___x_2945_);
v___x_2947_ = lean_unsigned_to_nat(65u);
v___x_2948_ = lean_nat_sub(v___x_2946_, v___x_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v_i_2940_);
v___x_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
}
v___jp_2951_:
{
if (v___y_2952_ == 0)
{
uint32_t v___x_2953_; uint8_t v___x_2954_; 
v___x_2953_ = 65;
v___x_2954_ = lean_uint32_dec_le(v___x_2953_, v_c_2939_);
if (v___x_2954_ == 0)
{
v___y_2942_ = v___x_2954_;
goto v___jp_2941_;
}
else
{
uint32_t v___x_2955_; uint8_t v___x_2956_; 
v___x_2955_ = 70;
v___x_2956_ = lean_uint32_dec_le(v_c_2939_, v___x_2955_);
v___y_2942_ = v___x_2956_;
goto v___jp_2941_;
}
}
else
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2957_ = lean_unsigned_to_nat(10u);
v___x_2958_ = lean_uint32_to_nat(v_c_2939_);
v___x_2959_ = lean_nat_add(v___x_2957_, v___x_2958_);
lean_dec(v___x_2958_);
v___x_2960_ = lean_unsigned_to_nat(97u);
v___x_2961_ = lean_nat_sub(v___x_2959_, v___x_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
lean_ctor_set(v___x_2962_, 1, v_i_2940_);
v___x_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
return v___x_2963_;
}
}
v___jp_2964_:
{
if (v___y_2965_ == 0)
{
uint32_t v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = 97;
v___x_2967_ = lean_uint32_dec_le(v___x_2966_, v_c_2939_);
if (v___x_2967_ == 0)
{
v___y_2952_ = v___x_2967_;
goto v___jp_2951_;
}
else
{
uint32_t v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = 102;
v___x_2969_ = lean_uint32_dec_le(v_c_2939_, v___x_2968_);
v___y_2952_ = v___x_2969_;
goto v___jp_2951_;
}
}
else
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2970_ = lean_uint32_to_nat(v_c_2939_);
v___x_2971_ = lean_unsigned_to_nat(48u);
v___x_2972_ = lean_nat_sub(v___x_2970_, v___x_2971_);
lean_dec(v___x_2970_);
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v_i_2940_);
v___x_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
return v___x_2974_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* v_s_2979_, lean_object* v_i_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2979_, v_i_2980_);
lean_dec(v_i_2980_);
lean_dec_ref(v_s_2979_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object* v_s_2982_, lean_object* v_i_2983_, lean_object* v_val_2984_){
_start:
{
uint8_t v___x_2985_; 
v___x_2985_ = lean_string_utf8_at_end(v_s_2982_, v_i_2983_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
v___x_2986_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2982_, v_i_2983_);
if (lean_obj_tag(v___x_2986_) == 0)
{
uint32_t v___x_2987_; uint32_t v___x_2988_; uint8_t v___x_2989_; 
v___x_2987_ = lean_string_utf8_get(v_s_2982_, v_i_2983_);
v___x_2988_ = 95;
v___x_2989_ = lean_uint32_dec_eq(v___x_2987_, v___x_2988_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; 
lean_dec(v_val_2984_);
lean_dec(v_i_2983_);
v___x_2990_ = lean_box(0);
return v___x_2990_;
}
else
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_string_utf8_next(v_s_2982_, v_i_2983_);
lean_dec(v_i_2983_);
v_i_2983_ = v___x_2991_;
goto _start;
}
}
else
{
lean_object* v_val_2993_; lean_object* v_fst_2994_; lean_object* v_snd_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_dec(v_i_2983_);
v_val_2993_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_val_2993_);
lean_dec_ref_known(v___x_2986_, 1);
v_fst_2994_ = lean_ctor_get(v_val_2993_, 0);
lean_inc(v_fst_2994_);
v_snd_2995_ = lean_ctor_get(v_val_2993_, 1);
lean_inc(v_snd_2995_);
lean_dec(v_val_2993_);
v___x_2996_ = lean_unsigned_to_nat(16u);
v___x_2997_ = lean_nat_mul(v___x_2996_, v_val_2984_);
lean_dec(v_val_2984_);
v___x_2998_ = lean_nat_add(v___x_2997_, v_fst_2994_);
lean_dec(v_fst_2994_);
lean_dec(v___x_2997_);
v_i_2983_ = v_snd_2995_;
v_val_2984_ = v___x_2998_;
goto _start;
}
}
else
{
lean_object* v___x_3000_; 
lean_dec(v_i_2983_);
v___x_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3000_, 0, v_val_2984_);
return v___x_3000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* v_s_3001_, lean_object* v_i_3002_, lean_object* v_val_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3001_, v_i_3002_, v_val_3003_);
lean_dec_ref(v_s_3001_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object* v_s_3005_, lean_object* v_i_3006_, lean_object* v_val_3007_){
_start:
{
uint8_t v___x_3008_; 
v___x_3008_ = lean_string_utf8_at_end(v_s_3005_, v_i_3006_);
if (v___x_3008_ == 0)
{
uint32_t v_c_3009_; uint8_t v___y_3011_; uint32_t v___x_3025_; uint8_t v___x_3026_; 
v_c_3009_ = lean_string_utf8_get(v_s_3005_, v_i_3006_);
v___x_3025_ = 48;
v___x_3026_ = lean_uint32_dec_le(v___x_3025_, v_c_3009_);
if (v___x_3026_ == 0)
{
v___y_3011_ = v___x_3026_;
goto v___jp_3010_;
}
else
{
uint32_t v___x_3027_; uint8_t v___x_3028_; 
v___x_3027_ = 57;
v___x_3028_ = lean_uint32_dec_le(v_c_3009_, v___x_3027_);
v___y_3011_ = v___x_3028_;
goto v___jp_3010_;
}
v___jp_3010_:
{
if (v___y_3011_ == 0)
{
uint32_t v___x_3012_; uint8_t v___x_3013_; 
v___x_3012_ = 95;
v___x_3013_ = lean_uint32_dec_eq(v_c_3009_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; 
lean_dec(v_val_3007_);
lean_dec(v_i_3006_);
v___x_3014_ = lean_box(0);
return v___x_3014_;
}
else
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_string_utf8_next(v_s_3005_, v_i_3006_);
lean_dec(v_i_3006_);
v_i_3006_ = v___x_3015_;
goto _start;
}
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3017_ = lean_string_utf8_next(v_s_3005_, v_i_3006_);
lean_dec(v_i_3006_);
v___x_3018_ = lean_unsigned_to_nat(10u);
v___x_3019_ = lean_nat_mul(v___x_3018_, v_val_3007_);
lean_dec(v_val_3007_);
v___x_3020_ = lean_uint32_to_nat(v_c_3009_);
v___x_3021_ = lean_nat_add(v___x_3019_, v___x_3020_);
lean_dec(v___x_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_unsigned_to_nat(48u);
v___x_3023_ = lean_nat_sub(v___x_3021_, v___x_3022_);
lean_dec(v___x_3021_);
v_i_3006_ = v___x_3017_;
v_val_3007_ = v___x_3023_;
goto _start;
}
}
}
else
{
lean_object* v___x_3029_; 
lean_dec(v_i_3006_);
v___x_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3029_, 0, v_val_3007_);
return v___x_3029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* v_s_3030_, lean_object* v_i_3031_, lean_object* v_val_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3030_, v_i_3031_, v_val_3032_);
lean_dec_ref(v_s_3030_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* v_s_3036_){
_start:
{
lean_object* v_len_3037_; lean_object* v___x_3038_; uint8_t v___y_3040_; uint8_t v___y_3053_; uint8_t v___x_3056_; 
v_len_3037_ = lean_string_length(v_s_3036_);
v___x_3038_ = lean_unsigned_to_nat(0u);
v___x_3056_ = lean_nat_dec_eq(v_len_3037_, v___x_3038_);
if (v___x_3056_ == 0)
{
uint32_t v_c_3057_; uint32_t v___x_3058_; uint8_t v___x_3059_; 
v_c_3057_ = lean_string_utf8_get(v_s_3036_, v___x_3038_);
v___x_3058_ = 48;
v___x_3059_ = lean_uint32_dec_eq(v_c_3057_, v___x_3058_);
if (v___x_3059_ == 0)
{
uint8_t v___x_3060_; 
lean_dec(v_len_3037_);
v___x_3060_ = lean_uint32_dec_le(v___x_3058_, v_c_3057_);
if (v___x_3060_ == 0)
{
v___y_3053_ = v___x_3060_;
goto v___jp_3052_;
}
else
{
uint32_t v___x_3061_; uint8_t v___x_3062_; 
v___x_3061_ = 57;
v___x_3062_ = lean_uint32_dec_le(v_c_3057_, v___x_3061_);
v___y_3053_ = v___x_3062_;
goto v___jp_3052_;
}
}
else
{
lean_object* v___x_3063_; uint8_t v___x_3064_; 
v___x_3063_ = lean_unsigned_to_nat(1u);
v___x_3064_ = lean_nat_dec_eq(v_len_3037_, v___x_3063_);
lean_dec(v_len_3037_);
if (v___x_3064_ == 0)
{
uint32_t v_c_3065_; uint32_t v___x_3066_; uint8_t v___x_3067_; 
v_c_3065_ = lean_string_utf8_get(v_s_3036_, v___x_3063_);
v___x_3066_ = 120;
v___x_3067_ = lean_uint32_dec_eq(v_c_3065_, v___x_3066_);
if (v___x_3067_ == 0)
{
uint32_t v___x_3068_; uint8_t v___x_3069_; 
v___x_3068_ = 88;
v___x_3069_ = lean_uint32_dec_eq(v_c_3065_, v___x_3068_);
if (v___x_3069_ == 0)
{
uint32_t v___x_3070_; uint8_t v___x_3071_; 
v___x_3070_ = 98;
v___x_3071_ = lean_uint32_dec_eq(v_c_3065_, v___x_3070_);
if (v___x_3071_ == 0)
{
uint32_t v___x_3072_; uint8_t v___x_3073_; 
v___x_3072_ = 66;
v___x_3073_ = lean_uint32_dec_eq(v_c_3065_, v___x_3072_);
if (v___x_3073_ == 0)
{
uint32_t v___x_3074_; uint8_t v___x_3075_; 
v___x_3074_ = 111;
v___x_3075_ = lean_uint32_dec_eq(v_c_3065_, v___x_3074_);
if (v___x_3075_ == 0)
{
uint32_t v___x_3076_; uint8_t v___x_3077_; 
v___x_3076_ = 79;
v___x_3077_ = lean_uint32_dec_eq(v_c_3065_, v___x_3076_);
if (v___x_3077_ == 0)
{
uint8_t v___x_3078_; 
v___x_3078_ = lean_uint32_dec_le(v___x_3058_, v_c_3065_);
if (v___x_3078_ == 0)
{
v___y_3040_ = v___x_3078_;
goto v___jp_3039_;
}
else
{
uint32_t v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = 57;
v___x_3080_ = lean_uint32_dec_le(v_c_3065_, v___x_3079_);
v___y_3040_ = v___x_3080_;
goto v___jp_3039_;
}
}
else
{
goto v___jp_3043_;
}
}
else
{
goto v___jp_3043_;
}
}
else
{
goto v___jp_3046_;
}
}
else
{
goto v___jp_3046_;
}
}
else
{
goto v___jp_3049_;
}
}
else
{
goto v___jp_3049_;
}
}
else
{
lean_object* v___x_3081_; 
v___x_3081_ = ((lean_object*)(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0));
return v___x_3081_;
}
}
}
else
{
lean_object* v___x_3082_; 
lean_dec(v_len_3037_);
v___x_3082_ = lean_box(0);
return v___x_3082_;
}
v___jp_3039_:
{
if (v___y_3040_ == 0)
{
lean_object* v___x_3041_; 
v___x_3041_ = lean_box(0);
return v___x_3041_;
}
else
{
lean_object* v___x_3042_; 
v___x_3042_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3036_, v___x_3038_, v___x_3038_);
return v___x_3042_;
}
}
v___jp_3043_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = lean_unsigned_to_nat(2u);
v___x_3045_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_3036_, v___x_3044_, v___x_3038_);
return v___x_3045_;
}
v___jp_3046_:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = lean_unsigned_to_nat(2u);
v___x_3048_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_3036_, v___x_3047_, v___x_3038_);
return v___x_3048_;
}
v___jp_3049_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_unsigned_to_nat(2u);
v___x_3051_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3036_, v___x_3050_, v___x_3038_);
return v___x_3051_;
}
v___jp_3052_:
{
if (v___y_3053_ == 0)
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_box(0);
return v___x_3054_;
}
else
{
lean_object* v___x_3055_; 
v___x_3055_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3036_, v___x_3038_, v___x_3038_);
return v___x_3055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* v_s_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_s_3083_);
lean_dec_ref(v_s_3083_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* v_litKind_3085_, lean_object* v_stx_3086_){
_start:
{
if (lean_obj_tag(v_stx_3086_) == 1)
{
lean_object* v_kind_3087_; lean_object* v_args_3088_; uint8_t v___x_3089_; 
v_kind_3087_ = lean_ctor_get(v_stx_3086_, 1);
v_args_3088_ = lean_ctor_get(v_stx_3086_, 2);
v___x_3089_ = lean_name_eq(v_kind_3087_, v_litKind_3085_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; 
v___x_3090_ = lean_box(0);
return v___x_3090_;
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3091_ = lean_array_get_size(v_args_3088_);
v___x_3092_ = lean_unsigned_to_nat(1u);
v___x_3093_ = lean_nat_dec_eq(v___x_3091_, v___x_3092_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; 
v___x_3094_ = lean_box(0);
return v___x_3094_;
}
else
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = lean_unsigned_to_nat(0u);
v___x_3096_ = lean_array_fget_borrowed(v_args_3088_, v___x_3095_);
if (lean_obj_tag(v___x_3096_) == 2)
{
lean_object* v_val_3097_; lean_object* v___x_3098_; 
v_val_3097_ = lean_ctor_get(v___x_3096_, 1);
lean_inc_ref(v_val_3097_);
v___x_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3098_, 0, v_val_3097_);
return v___x_3098_;
}
else
{
lean_object* v___x_3099_; 
v___x_3099_ = lean_box(0);
return v___x_3099_;
}
}
}
}
else
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_box(0);
return v___x_3100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* v_litKind_3101_, lean_object* v_stx_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_Syntax_isLit_x3f(v_litKind_3101_, v_stx_3102_);
lean_dec(v_stx_3102_);
lean_dec(v_litKind_3101_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object* v_litKind_3104_, lean_object* v_stx_3105_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_Syntax_isLit_x3f(v_litKind_3104_, v_stx_3105_);
if (lean_obj_tag(v___x_3106_) == 1)
{
lean_object* v_val_3107_; lean_object* v___x_3108_; 
v_val_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_val_3107_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3108_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_val_3107_);
lean_dec(v_val_3107_);
return v___x_3108_;
}
else
{
lean_object* v___x_3109_; 
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
return v___x_3109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object* v_litKind_3110_, lean_object* v_stx_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v_litKind_3110_, v_stx_3111_);
lean_dec(v_stx_3111_);
lean_dec(v_litKind_3110_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* v_s_3113_){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_3115_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3114_, v_s_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* v_s_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_Syntax_isNatLit_x3f(v_s_3116_);
lean_dec(v_s_3116_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* v_s_3121_){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = ((lean_object*)(l_Lean_Syntax_isFieldIdx_x3f___closed__1));
v___x_3123_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3122_, v_s_3121_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* v_s_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Lean_Syntax_isFieldIdx_x3f(v_s_3124_);
lean_dec(v_s_3124_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* v_s_3126_, lean_object* v_i_3127_, lean_object* v_val_3128_, lean_object* v_e_3129_, uint8_t v_sign_3130_, lean_object* v_exp_3131_){
_start:
{
uint8_t v___x_3132_; 
v___x_3132_ = lean_string_utf8_at_end(v_s_3126_, v_i_3127_);
if (v___x_3132_ == 0)
{
uint32_t v_c_3133_; uint8_t v___y_3135_; uint32_t v___x_3149_; uint8_t v___x_3150_; 
v_c_3133_ = lean_string_utf8_get(v_s_3126_, v_i_3127_);
v___x_3149_ = 48;
v___x_3150_ = lean_uint32_dec_le(v___x_3149_, v_c_3133_);
if (v___x_3150_ == 0)
{
v___y_3135_ = v___x_3150_;
goto v___jp_3134_;
}
else
{
uint32_t v___x_3151_; uint8_t v___x_3152_; 
v___x_3151_ = 57;
v___x_3152_ = lean_uint32_dec_le(v_c_3133_, v___x_3151_);
v___y_3135_ = v___x_3152_;
goto v___jp_3134_;
}
v___jp_3134_:
{
if (v___y_3135_ == 0)
{
uint32_t v___x_3136_; uint8_t v___x_3137_; 
v___x_3136_ = 95;
v___x_3137_ = lean_uint32_dec_eq(v_c_3133_, v___x_3136_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; 
lean_dec(v_exp_3131_);
lean_dec(v_val_3128_);
lean_dec(v_i_3127_);
v___x_3138_ = lean_box(0);
return v___x_3138_;
}
else
{
lean_object* v___x_3139_; 
v___x_3139_ = lean_string_utf8_next(v_s_3126_, v_i_3127_);
lean_dec(v_i_3127_);
v_i_3127_ = v___x_3139_;
goto _start;
}
}
else
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3141_ = lean_string_utf8_next(v_s_3126_, v_i_3127_);
lean_dec(v_i_3127_);
v___x_3142_ = lean_unsigned_to_nat(10u);
v___x_3143_ = lean_nat_mul(v___x_3142_, v_exp_3131_);
lean_dec(v_exp_3131_);
v___x_3144_ = lean_uint32_to_nat(v_c_3133_);
v___x_3145_ = lean_nat_add(v___x_3143_, v___x_3144_);
lean_dec(v___x_3144_);
lean_dec(v___x_3143_);
v___x_3146_ = lean_unsigned_to_nat(48u);
v___x_3147_ = lean_nat_sub(v___x_3145_, v___x_3146_);
lean_dec(v___x_3145_);
v_i_3127_ = v___x_3141_;
v_exp_3131_ = v___x_3147_;
goto _start;
}
}
}
else
{
lean_dec(v_i_3127_);
if (v_sign_3130_ == 0)
{
uint8_t v___x_3153_; 
v___x_3153_ = lean_nat_dec_le(v_e_3129_, v_exp_3131_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3154_ = lean_nat_sub(v_e_3129_, v_exp_3131_);
lean_dec(v_exp_3131_);
v___x_3155_ = lean_box(v___x_3132_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
lean_ctor_set(v___x_3156_, 1, v___x_3154_);
v___x_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3157_, 0, v_val_3128_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
return v___x_3158_;
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3159_ = lean_nat_sub(v_exp_3131_, v_e_3129_);
lean_dec(v_exp_3131_);
v___x_3160_ = lean_box(v_sign_3130_);
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
lean_ctor_set(v___x_3161_, 1, v___x_3159_);
v___x_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3162_, 0, v_val_3128_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3164_ = lean_nat_add(v_exp_3131_, v_e_3129_);
lean_dec(v_exp_3131_);
v___x_3165_ = lean_box(v_sign_3130_);
v___x_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3164_);
v___x_3167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3167_, 0, v_val_3128_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
return v___x_3168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* v_s_3169_, lean_object* v_i_3170_, lean_object* v_val_3171_, lean_object* v_e_3172_, lean_object* v_sign_3173_, lean_object* v_exp_3174_){
_start:
{
uint8_t v_sign_boxed_3175_; lean_object* v_res_3176_; 
v_sign_boxed_3175_ = lean_unbox(v_sign_3173_);
v_res_3176_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3169_, v_i_3170_, v_val_3171_, v_e_3172_, v_sign_boxed_3175_, v_exp_3174_);
lean_dec(v_e_3172_);
lean_dec_ref(v_s_3169_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* v_s_3177_, lean_object* v_i_3178_, lean_object* v_val_3179_, lean_object* v_e_3180_){
_start:
{
uint8_t v___x_3181_; 
v___x_3181_ = lean_string_utf8_at_end(v_s_3177_, v_i_3178_);
if (v___x_3181_ == 0)
{
uint32_t v_c_3182_; uint32_t v___x_3183_; uint8_t v___x_3184_; 
v_c_3182_ = lean_string_utf8_get(v_s_3177_, v_i_3178_);
v___x_3183_ = 45;
v___x_3184_ = lean_uint32_dec_eq(v_c_3182_, v___x_3183_);
if (v___x_3184_ == 0)
{
uint32_t v___x_3185_; uint8_t v___x_3186_; 
v___x_3185_ = 43;
v___x_3186_ = lean_uint32_dec_eq(v_c_3182_, v___x_3185_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_unsigned_to_nat(0u);
v___x_3188_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3177_, v_i_3178_, v_val_3179_, v_e_3180_, v___x_3186_, v___x_3187_);
return v___x_3188_;
}
else
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = lean_string_utf8_next(v_s_3177_, v_i_3178_);
lean_dec(v_i_3178_);
v___x_3190_ = lean_unsigned_to_nat(0u);
v___x_3191_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3177_, v___x_3189_, v_val_3179_, v_e_3180_, v___x_3184_, v___x_3190_);
return v___x_3191_;
}
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3192_ = lean_string_utf8_next(v_s_3177_, v_i_3178_);
lean_dec(v_i_3178_);
v___x_3193_ = lean_unsigned_to_nat(0u);
v___x_3194_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3177_, v___x_3192_, v_val_3179_, v_e_3180_, v___x_3184_, v___x_3193_);
return v___x_3194_;
}
}
else
{
lean_object* v___x_3195_; 
lean_dec(v_val_3179_);
lean_dec(v_i_3178_);
v___x_3195_ = lean_box(0);
return v___x_3195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* v_s_3196_, lean_object* v_i_3197_, lean_object* v_val_3198_, lean_object* v_e_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3196_, v_i_3197_, v_val_3198_, v_e_3199_);
lean_dec(v_e_3199_);
lean_dec_ref(v_s_3196_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* v_s_3201_, lean_object* v_i_3202_, lean_object* v_val_3203_, lean_object* v_e_3204_){
_start:
{
uint8_t v___x_3208_; 
v___x_3208_ = lean_string_utf8_at_end(v_s_3201_, v_i_3202_);
if (v___x_3208_ == 0)
{
uint32_t v_c_3209_; uint8_t v___y_3211_; uint32_t v___x_3231_; uint8_t v___x_3232_; 
v_c_3209_ = lean_string_utf8_get(v_s_3201_, v_i_3202_);
v___x_3231_ = 48;
v___x_3232_ = lean_uint32_dec_le(v___x_3231_, v_c_3209_);
if (v___x_3232_ == 0)
{
v___y_3211_ = v___x_3232_;
goto v___jp_3210_;
}
else
{
uint32_t v___x_3233_; uint8_t v___x_3234_; 
v___x_3233_ = 57;
v___x_3234_ = lean_uint32_dec_le(v_c_3209_, v___x_3233_);
v___y_3211_ = v___x_3234_;
goto v___jp_3210_;
}
v___jp_3210_:
{
if (v___y_3211_ == 0)
{
uint32_t v___x_3212_; uint8_t v___x_3213_; 
v___x_3212_ = 95;
v___x_3213_ = lean_uint32_dec_eq(v_c_3209_, v___x_3212_);
if (v___x_3213_ == 0)
{
uint32_t v___x_3214_; uint8_t v___x_3215_; 
v___x_3214_ = 101;
v___x_3215_ = lean_uint32_dec_eq(v_c_3209_, v___x_3214_);
if (v___x_3215_ == 0)
{
uint32_t v___x_3216_; uint8_t v___x_3217_; 
v___x_3216_ = 69;
v___x_3217_ = lean_uint32_dec_eq(v_c_3209_, v___x_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; 
lean_dec(v_e_3204_);
lean_dec(v_val_3203_);
lean_dec(v_i_3202_);
v___x_3218_ = lean_box(0);
return v___x_3218_;
}
else
{
goto v___jp_3205_;
}
}
else
{
goto v___jp_3205_;
}
}
else
{
lean_object* v___x_3219_; 
v___x_3219_ = lean_string_utf8_next(v_s_3201_, v_i_3202_);
lean_dec(v_i_3202_);
v_i_3202_ = v___x_3219_;
goto _start;
}
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3221_ = lean_string_utf8_next(v_s_3201_, v_i_3202_);
lean_dec(v_i_3202_);
v___x_3222_ = lean_unsigned_to_nat(10u);
v___x_3223_ = lean_nat_mul(v___x_3222_, v_val_3203_);
lean_dec(v_val_3203_);
v___x_3224_ = lean_uint32_to_nat(v_c_3209_);
v___x_3225_ = lean_nat_add(v___x_3223_, v___x_3224_);
lean_dec(v___x_3224_);
lean_dec(v___x_3223_);
v___x_3226_ = lean_unsigned_to_nat(48u);
v___x_3227_ = lean_nat_sub(v___x_3225_, v___x_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_unsigned_to_nat(1u);
v___x_3229_ = lean_nat_add(v_e_3204_, v___x_3228_);
lean_dec(v_e_3204_);
v_i_3202_ = v___x_3221_;
v_val_3203_ = v___x_3227_;
v_e_3204_ = v___x_3229_;
goto _start;
}
}
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_dec(v_i_3202_);
v___x_3235_ = lean_box(v___x_3208_);
v___x_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
lean_ctor_set(v___x_3236_, 1, v_e_3204_);
v___x_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3237_, 0, v_val_3203_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
v___x_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
return v___x_3238_;
}
v___jp_3205_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = lean_string_utf8_next(v_s_3201_, v_i_3202_);
lean_dec(v_i_3202_);
v___x_3207_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3201_, v___x_3206_, v_val_3203_, v_e_3204_);
lean_dec(v_e_3204_);
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* v_s_3239_, lean_object* v_i_3240_, lean_object* v_val_3241_, lean_object* v_e_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3239_, v_i_3240_, v_val_3241_, v_e_3242_);
lean_dec_ref(v_s_3239_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* v_s_3244_, lean_object* v_i_3245_, lean_object* v_val_3246_){
_start:
{
uint8_t v___x_3251_; 
v___x_3251_ = lean_string_utf8_at_end(v_s_3244_, v_i_3245_);
if (v___x_3251_ == 0)
{
uint32_t v_c_3252_; uint8_t v___y_3254_; uint32_t v___x_3277_; uint8_t v___x_3278_; 
v_c_3252_ = lean_string_utf8_get(v_s_3244_, v_i_3245_);
v___x_3277_ = 48;
v___x_3278_ = lean_uint32_dec_le(v___x_3277_, v_c_3252_);
if (v___x_3278_ == 0)
{
v___y_3254_ = v___x_3278_;
goto v___jp_3253_;
}
else
{
uint32_t v___x_3279_; uint8_t v___x_3280_; 
v___x_3279_ = 57;
v___x_3280_ = lean_uint32_dec_le(v_c_3252_, v___x_3279_);
v___y_3254_ = v___x_3280_;
goto v___jp_3253_;
}
v___jp_3253_:
{
if (v___y_3254_ == 0)
{
uint32_t v___x_3255_; uint8_t v___x_3256_; 
v___x_3255_ = 95;
v___x_3256_ = lean_uint32_dec_eq(v_c_3252_, v___x_3255_);
if (v___x_3256_ == 0)
{
uint32_t v___x_3257_; uint8_t v___x_3258_; 
v___x_3257_ = 46;
v___x_3258_ = lean_uint32_dec_eq(v_c_3252_, v___x_3257_);
if (v___x_3258_ == 0)
{
uint32_t v___x_3259_; uint8_t v___x_3260_; 
v___x_3259_ = 101;
v___x_3260_ = lean_uint32_dec_eq(v_c_3252_, v___x_3259_);
if (v___x_3260_ == 0)
{
uint32_t v___x_3261_; uint8_t v___x_3262_; 
v___x_3261_ = 69;
v___x_3262_ = lean_uint32_dec_eq(v_c_3252_, v___x_3261_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3263_; 
lean_dec(v_val_3246_);
lean_dec(v_i_3245_);
v___x_3263_ = lean_box(0);
return v___x_3263_;
}
else
{
goto v___jp_3247_;
}
}
else
{
goto v___jp_3247_;
}
}
else
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3264_ = lean_string_utf8_next(v_s_3244_, v_i_3245_);
lean_dec(v_i_3245_);
v___x_3265_ = lean_unsigned_to_nat(0u);
v___x_3266_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3244_, v___x_3264_, v_val_3246_, v___x_3265_);
return v___x_3266_;
}
}
else
{
lean_object* v___x_3267_; 
v___x_3267_ = lean_string_utf8_next(v_s_3244_, v_i_3245_);
lean_dec(v_i_3245_);
v_i_3245_ = v___x_3267_;
goto _start;
}
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3269_ = lean_string_utf8_next(v_s_3244_, v_i_3245_);
lean_dec(v_i_3245_);
v___x_3270_ = lean_unsigned_to_nat(10u);
v___x_3271_ = lean_nat_mul(v___x_3270_, v_val_3246_);
lean_dec(v_val_3246_);
v___x_3272_ = lean_uint32_to_nat(v_c_3252_);
v___x_3273_ = lean_nat_add(v___x_3271_, v___x_3272_);
lean_dec(v___x_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_unsigned_to_nat(48u);
v___x_3275_ = lean_nat_sub(v___x_3273_, v___x_3274_);
lean_dec(v___x_3273_);
v_i_3245_ = v___x_3269_;
v_val_3246_ = v___x_3275_;
goto _start;
}
}
}
else
{
lean_object* v___x_3281_; 
lean_dec(v_val_3246_);
lean_dec(v_i_3245_);
v___x_3281_ = lean_box(0);
return v___x_3281_;
}
v___jp_3247_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3248_ = lean_string_utf8_next(v_s_3244_, v_i_3245_);
lean_dec(v_i_3245_);
v___x_3249_ = lean_unsigned_to_nat(0u);
v___x_3250_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3244_, v___x_3248_, v_val_3246_, v___x_3249_);
return v___x_3250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* v_s_3282_, lean_object* v_i_3283_, lean_object* v_val_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3282_, v_i_3283_, v_val_3284_);
lean_dec_ref(v_s_3282_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* v_s_3286_){
_start:
{
lean_object* v_len_3287_; lean_object* v___x_3288_; uint8_t v___y_3290_; uint8_t v___x_3293_; 
v_len_3287_ = lean_string_length(v_s_3286_);
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3293_ = lean_nat_dec_eq(v_len_3287_, v___x_3288_);
lean_dec(v_len_3287_);
if (v___x_3293_ == 0)
{
uint32_t v_c_3294_; uint32_t v___x_3295_; uint8_t v___x_3296_; 
v_c_3294_ = lean_string_utf8_get(v_s_3286_, v___x_3288_);
v___x_3295_ = 48;
v___x_3296_ = lean_uint32_dec_le(v___x_3295_, v_c_3294_);
if (v___x_3296_ == 0)
{
v___y_3290_ = v___x_3296_;
goto v___jp_3289_;
}
else
{
uint32_t v___x_3297_; uint8_t v___x_3298_; 
v___x_3297_ = 57;
v___x_3298_ = lean_uint32_dec_le(v_c_3294_, v___x_3297_);
v___y_3290_ = v___x_3298_;
goto v___jp_3289_;
}
}
else
{
lean_object* v___x_3299_; 
v___x_3299_ = lean_box(0);
return v___x_3299_;
}
v___jp_3289_:
{
if (v___y_3290_ == 0)
{
lean_object* v___x_3291_; 
v___x_3291_ = lean_box(0);
return v___x_3291_;
}
else
{
lean_object* v___x_3292_; 
v___x_3292_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3286_, v___x_3288_, v___x_3288_);
return v___x_3292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* v_s_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_s_3300_);
lean_dec_ref(v_s_3300_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* v_stx_3302_){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_3304_ = l_Lean_Syntax_isLit_x3f(v___x_3303_, v_stx_3302_);
if (lean_obj_tag(v___x_3304_) == 1)
{
lean_object* v_val_3305_; lean_object* v___x_3306_; 
v_val_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_val_3305_);
lean_dec_ref_known(v___x_3304_, 1);
v___x_3306_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_val_3305_);
lean_dec(v_val_3305_);
return v___x_3306_;
}
else
{
lean_object* v___x_3307_; 
lean_dec(v___x_3304_);
v___x_3307_ = lean_box(0);
return v___x_3307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* v_stx_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_Syntax_isScientificLit_x3f(v_stx_3308_);
lean_dec(v_stx_3308_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* v_x_3310_){
_start:
{
switch(lean_obj_tag(v_x_3310_))
{
case 2:
{
lean_object* v_val_3311_; lean_object* v___x_3312_; 
v_val_3311_ = lean_ctor_get(v_x_3310_, 1);
lean_inc_ref(v_val_3311_);
lean_dec_ref_known(v_x_3310_, 2);
v___x_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3312_, 0, v_val_3311_);
return v___x_3312_;
}
case 3:
{
lean_object* v_rawVal_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v_rawVal_3313_ = lean_ctor_get(v_x_3310_, 1);
lean_inc_ref(v_rawVal_3313_);
lean_dec_ref_known(v_x_3310_, 4);
v___x_3314_ = lean_substring_tostring(v_rawVal_3313_);
v___x_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
return v___x_3315_;
}
default: 
{
lean_object* v___x_3316_; 
lean_dec(v_x_3310_);
v___x_3316_ = lean_box(0);
return v___x_3316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* v_stx_3317_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Lean_Syntax_isNatLit_x3f(v_stx_3317_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_unsigned_to_nat(0u);
return v___x_3319_;
}
else
{
lean_object* v_val_3320_; 
v_val_3320_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_val_3320_);
lean_dec_ref_known(v___x_3318_, 1);
return v_val_3320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* v_stx_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_Syntax_toNat(v_stx_3321_);
lean_dec(v_stx_3321_);
return v_res_3322_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = 9;
v___x_3324_ = lean_box_uint32(v___x_3323_);
return v___x_3324_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = 10;
v___x_3326_ = lean_box_uint32(v___x_3325_);
return v___x_3326_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = 13;
v___x_3328_ = lean_box_uint32(v___x_3327_);
return v___x_3328_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = 39;
v___x_3330_ = lean_box_uint32(v___x_3329_);
return v___x_3330_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = 34;
v___x_3332_ = lean_box_uint32(v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = 92;
v___x_3334_ = lean_box_uint32(v___x_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* v_s_3335_, lean_object* v_i_3336_){
_start:
{
uint32_t v_c_3337_; lean_object* v_i_3338_; uint32_t v___x_3339_; uint8_t v___x_3340_; 
v_c_3337_ = lean_string_utf8_get(v_s_3335_, v_i_3336_);
v_i_3338_ = lean_string_utf8_next(v_s_3335_, v_i_3336_);
v___x_3339_ = 92;
v___x_3340_ = lean_uint32_dec_eq(v_c_3337_, v___x_3339_);
if (v___x_3340_ == 0)
{
uint32_t v___x_3341_; uint8_t v___x_3342_; 
v___x_3341_ = 34;
v___x_3342_ = lean_uint32_dec_eq(v_c_3337_, v___x_3341_);
if (v___x_3342_ == 0)
{
uint32_t v___x_3343_; uint8_t v___x_3344_; 
v___x_3343_ = 39;
v___x_3344_ = lean_uint32_dec_eq(v_c_3337_, v___x_3343_);
if (v___x_3344_ == 0)
{
uint32_t v___x_3345_; uint8_t v___x_3346_; 
v___x_3345_ = 114;
v___x_3346_ = lean_uint32_dec_eq(v_c_3337_, v___x_3345_);
if (v___x_3346_ == 0)
{
uint32_t v___x_3347_; uint8_t v___x_3348_; 
v___x_3347_ = 110;
v___x_3348_ = lean_uint32_dec_eq(v_c_3337_, v___x_3347_);
if (v___x_3348_ == 0)
{
uint32_t v___x_3349_; uint8_t v___x_3350_; 
v___x_3349_ = 116;
v___x_3350_ = lean_uint32_dec_eq(v_c_3337_, v___x_3349_);
if (v___x_3350_ == 0)
{
uint32_t v___x_3351_; uint8_t v___x_3352_; 
v___x_3351_ = 120;
v___x_3352_ = lean_uint32_dec_eq(v_c_3337_, v___x_3351_);
if (v___x_3352_ == 0)
{
uint32_t v___x_3353_; uint8_t v___x_3354_; 
v___x_3353_ = 117;
v___x_3354_ = lean_uint32_dec_eq(v_c_3337_, v___x_3353_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
lean_dec(v_i_3338_);
v___x_3355_ = lean_box(0);
return v___x_3355_;
}
else
{
lean_object* v___x_3356_; 
v___x_3356_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3335_, v_i_3338_);
lean_dec(v_i_3338_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_box(0);
return v___x_3357_;
}
else
{
lean_object* v_val_3358_; lean_object* v_fst_3359_; lean_object* v_snd_3360_; lean_object* v___x_3361_; 
v_val_3358_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_val_3358_);
lean_dec_ref_known(v___x_3356_, 1);
v_fst_3359_ = lean_ctor_get(v_val_3358_, 0);
lean_inc(v_fst_3359_);
v_snd_3360_ = lean_ctor_get(v_val_3358_, 1);
lean_inc(v_snd_3360_);
lean_dec(v_val_3358_);
v___x_3361_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3335_, v_snd_3360_);
lean_dec(v_snd_3360_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v___x_3362_; 
lean_dec(v_fst_3359_);
v___x_3362_ = lean_box(0);
return v___x_3362_;
}
else
{
lean_object* v_val_3363_; lean_object* v_fst_3364_; lean_object* v_snd_3365_; lean_object* v___x_3366_; 
v_val_3363_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_val_3363_);
lean_dec_ref_known(v___x_3361_, 1);
v_fst_3364_ = lean_ctor_get(v_val_3363_, 0);
lean_inc(v_fst_3364_);
v_snd_3365_ = lean_ctor_get(v_val_3363_, 1);
lean_inc(v_snd_3365_);
lean_dec(v_val_3363_);
v___x_3366_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3335_, v_snd_3365_);
lean_dec(v_snd_3365_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v___x_3367_; 
lean_dec(v_fst_3364_);
lean_dec(v_fst_3359_);
v___x_3367_ = lean_box(0);
return v___x_3367_;
}
else
{
lean_object* v_val_3368_; lean_object* v_fst_3369_; lean_object* v_snd_3370_; lean_object* v___x_3371_; 
v_val_3368_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_val_3368_);
lean_dec_ref_known(v___x_3366_, 1);
v_fst_3369_ = lean_ctor_get(v_val_3368_, 0);
lean_inc(v_fst_3369_);
v_snd_3370_ = lean_ctor_get(v_val_3368_, 1);
lean_inc(v_snd_3370_);
lean_dec(v_val_3368_);
v___x_3371_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3335_, v_snd_3370_);
lean_dec(v_snd_3370_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v___x_3372_; 
lean_dec(v_fst_3369_);
lean_dec(v_fst_3364_);
lean_dec(v_fst_3359_);
v___x_3372_ = lean_box(0);
return v___x_3372_;
}
else
{
lean_object* v_val_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3398_; 
v_val_3373_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3375_ = v___x_3371_;
v_isShared_3376_ = v_isSharedCheck_3398_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_val_3373_);
lean_dec(v___x_3371_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3398_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v_fst_3377_; lean_object* v_snd_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3397_; 
v_fst_3377_ = lean_ctor_get(v_val_3373_, 0);
v_snd_3378_ = lean_ctor_get(v_val_3373_, 1);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_val_3373_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3380_ = v_val_3373_;
v_isShared_3381_ = v_isSharedCheck_3397_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_snd_3378_);
lean_inc(v_fst_3377_);
lean_dec(v_val_3373_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3397_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; uint32_t v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3382_ = lean_unsigned_to_nat(16u);
v___x_3383_ = lean_nat_mul(v___x_3382_, v_fst_3359_);
lean_dec(v_fst_3359_);
v___x_3384_ = lean_nat_add(v___x_3383_, v_fst_3364_);
lean_dec(v_fst_3364_);
lean_dec(v___x_3383_);
v___x_3385_ = lean_nat_mul(v___x_3382_, v___x_3384_);
lean_dec(v___x_3384_);
v___x_3386_ = lean_nat_add(v___x_3385_, v_fst_3369_);
lean_dec(v_fst_3369_);
lean_dec(v___x_3385_);
v___x_3387_ = lean_nat_mul(v___x_3382_, v___x_3386_);
lean_dec(v___x_3386_);
v___x_3388_ = lean_nat_add(v___x_3387_, v_fst_3377_);
lean_dec(v_fst_3377_);
lean_dec(v___x_3387_);
v___x_3389_ = l_Char_ofNat(v___x_3388_);
lean_dec(v___x_3388_);
v___x_3390_ = lean_box_uint32(v___x_3389_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v___x_3390_);
v___x_3392_ = v___x_3380_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_snd_3378_);
v___x_3392_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3394_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3392_);
v___x_3394_ = v___x_3375_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
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
else
{
lean_object* v___x_3399_; 
v___x_3399_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3335_, v_i_3338_);
lean_dec(v_i_3338_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v___x_3400_; 
v___x_3400_ = lean_box(0);
return v___x_3400_;
}
else
{
lean_object* v_val_3401_; lean_object* v_fst_3402_; lean_object* v_snd_3403_; lean_object* v___x_3404_; 
v_val_3401_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_val_3401_);
lean_dec_ref_known(v___x_3399_, 1);
v_fst_3402_ = lean_ctor_get(v_val_3401_, 0);
lean_inc(v_fst_3402_);
v_snd_3403_ = lean_ctor_get(v_val_3401_, 1);
lean_inc(v_snd_3403_);
lean_dec(v_val_3401_);
v___x_3404_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3335_, v_snd_3403_);
lean_dec(v_snd_3403_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v___x_3405_; 
lean_dec(v_fst_3402_);
v___x_3405_ = lean_box(0);
return v___x_3405_;
}
else
{
lean_object* v_val_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3427_; 
v_val_3406_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3408_ = v___x_3404_;
v_isShared_3409_ = v_isSharedCheck_3427_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_val_3406_);
lean_dec(v___x_3404_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3427_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v_fst_3410_; lean_object* v_snd_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3426_; 
v_fst_3410_ = lean_ctor_get(v_val_3406_, 0);
v_snd_3411_ = lean_ctor_get(v_val_3406_, 1);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_val_3406_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3413_ = v_val_3406_;
v_isShared_3414_ = v_isSharedCheck_3426_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_snd_3411_);
lean_inc(v_fst_3410_);
lean_dec(v_val_3406_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3426_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; uint32_t v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3421_; 
v___x_3415_ = lean_unsigned_to_nat(16u);
v___x_3416_ = lean_nat_mul(v___x_3415_, v_fst_3402_);
lean_dec(v_fst_3402_);
v___x_3417_ = lean_nat_add(v___x_3416_, v_fst_3410_);
lean_dec(v_fst_3410_);
lean_dec(v___x_3416_);
v___x_3418_ = l_Char_ofNat(v___x_3417_);
lean_dec(v___x_3417_);
v___x_3419_ = lean_box_uint32(v___x_3418_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 0, v___x_3419_);
v___x_3421_ = v___x_3413_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_snd_3411_);
v___x_3421_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
lean_object* v___x_3423_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v___x_3421_);
v___x_3423_ = v___x_3408_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
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
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3428_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
v___x_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
lean_ctor_set(v___x_3429_, 1, v_i_3338_);
v___x_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
return v___x_3430_;
}
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3431_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
v___x_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
lean_ctor_set(v___x_3432_, 1, v_i_3338_);
v___x_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3432_);
return v___x_3433_;
}
}
else
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3434_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
v___x_3435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
lean_ctor_set(v___x_3435_, 1, v_i_3338_);
v___x_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
return v___x_3436_;
}
}
else
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3437_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
v___x_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
lean_ctor_set(v___x_3438_, 1, v_i_3338_);
v___x_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
return v___x_3439_;
}
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3440_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
v___x_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
lean_ctor_set(v___x_3441_, 1, v_i_3338_);
v___x_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
return v___x_3442_;
}
}
else
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3443_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
v___x_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
lean_ctor_set(v___x_3444_, 1, v_i_3338_);
v___x_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
return v___x_3445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* v_s_3446_, lean_object* v_i_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Lean_Syntax_decodeQuotedChar(v_s_3446_, v_i_3447_);
lean_dec(v_i_3447_);
lean_dec_ref(v_s_3446_);
return v_res_3448_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t v___y_3449_){
_start:
{
uint8_t v___y_3451_; uint32_t v___x_3456_; uint8_t v___x_3457_; 
v___x_3456_ = 32;
v___x_3457_ = lean_uint32_dec_eq(v___y_3449_, v___x_3456_);
if (v___x_3457_ == 0)
{
uint32_t v___x_3458_; uint8_t v___x_3459_; 
v___x_3458_ = 9;
v___x_3459_ = lean_uint32_dec_eq(v___y_3449_, v___x_3458_);
v___y_3451_ = v___x_3459_;
goto v___jp_3450_;
}
else
{
v___y_3451_ = v___x_3457_;
goto v___jp_3450_;
}
v___jp_3450_:
{
if (v___y_3451_ == 0)
{
uint32_t v___x_3452_; uint8_t v___x_3453_; 
v___x_3452_ = 13;
v___x_3453_ = lean_uint32_dec_eq(v___y_3449_, v___x_3452_);
if (v___x_3453_ == 0)
{
uint32_t v___x_3454_; uint8_t v___x_3455_; 
v___x_3454_ = 10;
v___x_3455_ = lean_uint32_dec_eq(v___y_3449_, v___x_3454_);
return v___x_3455_;
}
else
{
return v___x_3453_;
}
}
else
{
return v___y_3451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* v___y_3460_){
_start:
{
uint32_t v___y_233__boxed_3461_; uint8_t v_res_3462_; lean_object* v_r_3463_; 
v___y_233__boxed_3461_ = lean_unbox_uint32(v___y_3460_);
lean_dec(v___y_3460_);
v_res_3462_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_233__boxed_3461_);
v_r_3463_ = lean_box(v_res_3462_);
return v_r_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* v_s_3465_, lean_object* v_i_3466_){
_start:
{
lean_object* v___f_3467_; uint8_t v___y_3473_; uint32_t v___x_3475_; uint8_t v___y_3477_; uint32_t v___x_3482_; uint8_t v___x_3483_; 
v___f_3467_ = ((lean_object*)(l_Lean_Syntax_decodeStringGap___closed__0));
v___x_3475_ = lean_string_utf8_get(v_s_3465_, v_i_3466_);
v___x_3482_ = 32;
v___x_3483_ = lean_uint32_dec_eq(v___x_3475_, v___x_3482_);
if (v___x_3483_ == 0)
{
uint32_t v___x_3484_; uint8_t v___x_3485_; 
v___x_3484_ = 9;
v___x_3485_ = lean_uint32_dec_eq(v___x_3475_, v___x_3484_);
v___y_3477_ = v___x_3485_;
goto v___jp_3476_;
}
else
{
v___y_3477_ = v___x_3483_;
goto v___jp_3476_;
}
v___jp_3468_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3469_ = lean_string_utf8_next(v_s_3465_, v_i_3466_);
v___x_3470_ = lean_string_nextwhile(v_s_3465_, v___f_3467_, v___x_3469_);
v___x_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
return v___x_3471_;
}
v___jp_3472_:
{
if (v___y_3473_ == 0)
{
lean_object* v___x_3474_; 
lean_dec_ref(v_s_3465_);
v___x_3474_ = lean_box(0);
return v___x_3474_;
}
else
{
goto v___jp_3468_;
}
}
v___jp_3476_:
{
if (v___y_3477_ == 0)
{
uint32_t v___x_3478_; uint8_t v___x_3479_; 
v___x_3478_ = 13;
v___x_3479_ = lean_uint32_dec_eq(v___x_3475_, v___x_3478_);
if (v___x_3479_ == 0)
{
uint32_t v___x_3480_; uint8_t v___x_3481_; 
v___x_3480_ = 10;
v___x_3481_ = lean_uint32_dec_eq(v___x_3475_, v___x_3480_);
v___y_3473_ = v___x_3481_;
goto v___jp_3472_;
}
else
{
v___y_3473_ = v___x_3479_;
goto v___jp_3472_;
}
}
else
{
goto v___jp_3468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* v_s_3486_, lean_object* v_i_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Lean_Syntax_decodeStringGap(v_s_3486_, v_i_3487_);
lean_dec(v_i_3487_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* v_s_3489_, lean_object* v_i_3490_, lean_object* v_acc_3491_){
_start:
{
uint32_t v_c_3492_; uint32_t v___x_3493_; uint8_t v___x_3494_; 
v_c_3492_ = lean_string_utf8_get(v_s_3489_, v_i_3490_);
v___x_3493_ = 34;
v___x_3494_ = lean_uint32_dec_eq(v_c_3492_, v___x_3493_);
if (v___x_3494_ == 0)
{
lean_object* v_i_3495_; uint8_t v___x_3496_; 
v_i_3495_ = lean_string_utf8_next(v_s_3489_, v_i_3490_);
lean_dec(v_i_3490_);
v___x_3496_ = lean_string_utf8_at_end(v_s_3489_, v_i_3495_);
if (v___x_3496_ == 0)
{
uint32_t v___x_3497_; uint8_t v___x_3498_; 
v___x_3497_ = 92;
v___x_3498_ = lean_uint32_dec_eq(v_c_3492_, v___x_3497_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
v___x_3499_ = lean_string_push(v_acc_3491_, v_c_3492_);
v_i_3490_ = v_i_3495_;
v_acc_3491_ = v___x_3499_;
goto _start;
}
else
{
lean_object* v___x_3501_; 
v___x_3501_ = l_Lean_Syntax_decodeQuotedChar(v_s_3489_, v_i_3495_);
if (lean_obj_tag(v___x_3501_) == 1)
{
lean_object* v_val_3502_; lean_object* v_fst_3503_; lean_object* v_snd_3504_; uint32_t v___x_3505_; lean_object* v___x_3506_; 
lean_dec(v_i_3495_);
v_val_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_val_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v_fst_3503_ = lean_ctor_get(v_val_3502_, 0);
lean_inc(v_fst_3503_);
v_snd_3504_ = lean_ctor_get(v_val_3502_, 1);
lean_inc(v_snd_3504_);
lean_dec(v_val_3502_);
v___x_3505_ = lean_unbox_uint32(v_fst_3503_);
lean_dec(v_fst_3503_);
v___x_3506_ = lean_string_push(v_acc_3491_, v___x_3505_);
v_i_3490_ = v_snd_3504_;
v_acc_3491_ = v___x_3506_;
goto _start;
}
else
{
lean_object* v___x_3508_; 
lean_dec(v___x_3501_);
lean_inc_ref(v_s_3489_);
v___x_3508_ = l_Lean_Syntax_decodeStringGap(v_s_3489_, v_i_3495_);
lean_dec(v_i_3495_);
if (lean_obj_tag(v___x_3508_) == 1)
{
lean_object* v_val_3509_; 
v_val_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_val_3509_);
lean_dec_ref_known(v___x_3508_, 1);
v_i_3490_ = v_val_3509_;
goto _start;
}
else
{
lean_object* v___x_3511_; 
lean_dec(v___x_3508_);
lean_dec_ref(v_acc_3491_);
lean_dec_ref(v_s_3489_);
v___x_3511_ = lean_box(0);
return v___x_3511_;
}
}
}
}
else
{
lean_object* v___x_3512_; 
lean_dec(v_i_3495_);
lean_dec_ref(v_acc_3491_);
lean_dec_ref(v_s_3489_);
v___x_3512_ = lean_box(0);
return v___x_3512_;
}
}
else
{
lean_object* v___x_3513_; 
lean_dec(v_i_3490_);
lean_dec_ref(v_s_3489_);
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v_acc_3491_);
return v___x_3513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* v_s_3514_, lean_object* v_i_3515_, lean_object* v_num_3516_){
_start:
{
uint32_t v_c_3517_; lean_object* v_i_3518_; uint32_t v___x_3519_; uint8_t v___x_3520_; 
v_c_3517_ = lean_string_utf8_get(v_s_3514_, v_i_3515_);
v_i_3518_ = lean_string_utf8_next(v_s_3514_, v_i_3515_);
lean_dec(v_i_3515_);
v___x_3519_ = 35;
v___x_3520_ = lean_uint32_dec_eq(v_c_3517_, v___x_3519_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3521_ = lean_string_utf8_byte_size(v_s_3514_);
v___x_3522_ = lean_unsigned_to_nat(1u);
v___x_3523_ = lean_nat_add(v_num_3516_, v___x_3522_);
lean_dec(v_num_3516_);
v___x_3524_ = lean_nat_sub(v___x_3521_, v___x_3523_);
lean_dec(v___x_3523_);
v___x_3525_ = lean_string_utf8_extract(v_s_3514_, v_i_3518_, v___x_3524_);
lean_dec(v___x_3524_);
lean_dec(v_i_3518_);
return v___x_3525_;
}
else
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = lean_unsigned_to_nat(1u);
v___x_3527_ = lean_nat_add(v_num_3516_, v___x_3526_);
lean_dec(v_num_3516_);
v_i_3515_ = v_i_3518_;
v_num_3516_ = v___x_3527_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* v_s_3529_, lean_object* v_i_3530_, lean_object* v_num_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3529_, v_i_3530_, v_num_3531_);
lean_dec_ref(v_s_3529_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* v_s_3533_){
_start:
{
lean_object* v___x_3534_; uint32_t v___x_3535_; uint32_t v___x_3536_; uint8_t v___x_3537_; 
v___x_3534_ = lean_unsigned_to_nat(0u);
v___x_3535_ = lean_string_utf8_get(v_s_3533_, v___x_3534_);
v___x_3536_ = 114;
v___x_3537_ = lean_uint32_dec_eq(v___x_3535_, v___x_3536_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = lean_unsigned_to_nat(1u);
v___x_3539_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_3540_ = l_Lean_Syntax_decodeStrLitAux(v_s_3533_, v___x_3538_, v___x_3539_);
return v___x_3540_;
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = lean_unsigned_to_nat(1u);
v___x_3542_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3533_, v___x_3541_, v___x_3534_);
lean_dec_ref(v_s_3533_);
v___x_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
return v___x_3543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* v_stx_3544_){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_3546_ = l_Lean_Syntax_isLit_x3f(v___x_3545_, v_stx_3544_);
if (lean_obj_tag(v___x_3546_) == 1)
{
lean_object* v_val_3547_; lean_object* v___x_3548_; 
v_val_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_val_3547_);
lean_dec_ref_known(v___x_3546_, 1);
v___x_3548_ = l_Lean_Syntax_decodeStrLit(v_val_3547_);
return v___x_3548_;
}
else
{
lean_object* v___x_3549_; 
lean_dec(v___x_3546_);
v___x_3549_ = lean_box(0);
return v___x_3549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* v_stx_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l_Lean_Syntax_isStrLit_x3f(v_stx_3550_);
lean_dec(v_stx_3550_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* v_s_3552_){
_start:
{
lean_object* v___x_3553_; uint32_t v_c_3554_; uint32_t v___x_3555_; uint8_t v___x_3556_; 
v___x_3553_ = lean_unsigned_to_nat(1u);
v_c_3554_ = lean_string_utf8_get(v_s_3552_, v___x_3553_);
v___x_3555_ = 92;
v___x_3556_ = lean_uint32_dec_eq(v_c_3554_, v___x_3555_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = lean_box_uint32(v_c_3554_);
v___x_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
return v___x_3558_;
}
else
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = lean_unsigned_to_nat(2u);
v___x_3560_ = l_Lean_Syntax_decodeQuotedChar(v_s_3552_, v___x_3559_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v___x_3561_; 
v___x_3561_ = lean_box(0);
return v___x_3561_;
}
else
{
lean_object* v_val_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3570_; 
v_val_3562_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3564_ = v___x_3560_;
v_isShared_3565_ = v_isSharedCheck_3570_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_val_3562_);
lean_dec(v___x_3560_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3570_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v_fst_3566_; lean_object* v___x_3568_; 
v_fst_3566_ = lean_ctor_get(v_val_3562_, 0);
lean_inc(v_fst_3566_);
lean_dec(v_val_3562_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v_fst_3566_);
v___x_3568_ = v___x_3564_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_fst_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* v_s_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Lean_Syntax_decodeCharLit(v_s_3571_);
lean_dec_ref(v_s_3571_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* v_stx_3573_){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_3575_ = l_Lean_Syntax_isLit_x3f(v___x_3574_, v_stx_3573_);
if (lean_obj_tag(v___x_3575_) == 1)
{
lean_object* v_val_3576_; lean_object* v___x_3577_; 
v_val_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_val_3576_);
lean_dec_ref_known(v___x_3575_, 1);
v___x_3577_ = l_Lean_Syntax_decodeCharLit(v_val_3576_);
lean_dec(v_val_3576_);
return v___x_3577_;
}
else
{
lean_object* v___x_3578_; 
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
return v___x_3578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* v_stx_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_Syntax_isCharLit_x3f(v_stx_3579_);
lean_dec(v_stx_3579_);
return v_res_3580_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t v___y_3581_){
_start:
{
uint8_t v___y_3583_; uint8_t v___y_3595_; uint32_t v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = 65;
v___x_3606_ = lean_uint32_dec_le(v___x_3605_, v___y_3581_);
if (v___x_3606_ == 0)
{
goto v___jp_3600_;
}
else
{
uint32_t v___x_3607_; uint8_t v___x_3608_; 
v___x_3607_ = 90;
v___x_3608_ = lean_uint32_dec_le(v___y_3581_, v___x_3607_);
if (v___x_3608_ == 0)
{
goto v___jp_3600_;
}
else
{
return v___x_3608_;
}
}
v___jp_3582_:
{
if (v___y_3583_ == 0)
{
uint32_t v___x_3584_; uint8_t v___x_3585_; 
v___x_3584_ = 95;
v___x_3585_ = lean_uint32_dec_eq(v___y_3581_, v___x_3584_);
if (v___x_3585_ == 0)
{
uint32_t v___x_3586_; uint8_t v___x_3587_; 
v___x_3586_ = 39;
v___x_3587_ = lean_uint32_dec_eq(v___y_3581_, v___x_3586_);
if (v___x_3587_ == 0)
{
uint32_t v___x_3588_; uint8_t v___x_3589_; 
v___x_3588_ = 33;
v___x_3589_ = lean_uint32_dec_eq(v___y_3581_, v___x_3588_);
if (v___x_3589_ == 0)
{
uint32_t v___x_3590_; uint8_t v___x_3591_; 
v___x_3590_ = 63;
v___x_3591_ = lean_uint32_dec_eq(v___y_3581_, v___x_3590_);
if (v___x_3591_ == 0)
{
uint8_t v___x_3592_; 
v___x_3592_ = l_Lean_isLetterLike(v___y_3581_);
if (v___x_3592_ == 0)
{
uint8_t v___x_3593_; 
v___x_3593_ = l_Lean_isSubScriptAlnum(v___y_3581_);
return v___x_3593_;
}
else
{
return v___x_3592_;
}
}
else
{
return v___x_3591_;
}
}
else
{
return v___x_3589_;
}
}
else
{
return v___x_3587_;
}
}
else
{
return v___x_3585_;
}
}
else
{
return v___y_3583_;
}
}
v___jp_3594_:
{
if (v___y_3595_ == 0)
{
uint32_t v___x_3596_; uint8_t v___x_3597_; 
v___x_3596_ = 48;
v___x_3597_ = lean_uint32_dec_le(v___x_3596_, v___y_3581_);
if (v___x_3597_ == 0)
{
v___y_3583_ = v___x_3597_;
goto v___jp_3582_;
}
else
{
uint32_t v___x_3598_; uint8_t v___x_3599_; 
v___x_3598_ = 57;
v___x_3599_ = lean_uint32_dec_le(v___y_3581_, v___x_3598_);
v___y_3583_ = v___x_3599_;
goto v___jp_3582_;
}
}
else
{
return v___y_3595_;
}
}
v___jp_3600_:
{
uint32_t v___x_3601_; uint8_t v___x_3602_; 
v___x_3601_ = 97;
v___x_3602_ = lean_uint32_dec_le(v___x_3601_, v___y_3581_);
if (v___x_3602_ == 0)
{
v___y_3595_ = v___x_3602_;
goto v___jp_3594_;
}
else
{
uint32_t v___x_3603_; uint8_t v___x_3604_; 
v___x_3603_ = 122;
v___x_3604_ = lean_uint32_dec_le(v___y_3581_, v___x_3603_);
v___y_3595_ = v___x_3604_;
goto v___jp_3594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* v___y_3609_){
_start:
{
uint32_t v___y_1112__boxed_3610_; uint8_t v_res_3611_; lean_object* v_r_3612_; 
v___y_1112__boxed_3610_ = lean_unbox_uint32(v___y_3609_);
lean_dec(v___y_3609_);
v_res_3611_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_1112__boxed_3610_);
v_r_3612_ = lean_box(v_res_3611_);
return v_r_3612_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t v___y_3613_){
_start:
{
uint32_t v___x_3614_; uint8_t v___x_3615_; 
v___x_3614_ = 48;
v___x_3615_ = lean_uint32_dec_le(v___x_3614_, v___y_3613_);
if (v___x_3615_ == 0)
{
return v___x_3615_;
}
else
{
uint32_t v___x_3616_; uint8_t v___x_3617_; 
v___x_3616_ = 57;
v___x_3617_ = lean_uint32_dec_le(v___y_3613_, v___x_3616_);
return v___x_3617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* v___y_3618_){
_start:
{
uint32_t v___y_1169__boxed_3619_; uint8_t v_res_3620_; lean_object* v_r_3621_; 
v___y_1169__boxed_3619_ = lean_unbox_uint32(v___y_3618_);
lean_dec(v___y_3618_);
v_res_3620_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___y_1169__boxed_3619_);
v_r_3621_ = lean_box(v_res_3620_);
return v_r_3621_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint32_t v_x_3622_){
_start:
{
uint32_t v___x_3623_; uint8_t v___x_3624_; uint8_t v___x_3625_; 
v___x_3623_ = 187;
v___x_3624_ = lean_uint32_dec_eq(v_x_3622_, v___x_3623_);
v___x_3625_ = lean_bool_not(v___x_3624_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* v_x_3626_){
_start:
{
uint32_t v_x_1180__boxed_3627_; uint8_t v_res_3628_; lean_object* v_r_3629_; 
v_x_1180__boxed_3627_ = lean_unbox_uint32(v_x_3626_);
lean_dec(v_x_3626_);
v_res_3628_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v_x_1180__boxed_3627_);
v_r_3629_ = lean_box(v_res_3628_);
return v_r_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* v_ss_3633_, lean_object* v_acc_3634_){
_start:
{
lean_object* v_ss_3636_; lean_object* v_acc_3637_; uint8_t v___x_3646_; 
lean_inc_ref(v_ss_3633_);
v___x_3646_ = lean_substring_isempty(v_ss_3633_);
if (v___x_3646_ == 0)
{
uint32_t v_curr_3647_; uint32_t v___x_3648_; uint8_t v___x_3649_; 
lean_inc_ref(v_ss_3633_);
v_curr_3647_ = lean_substring_front(v_ss_3633_);
v___x_3648_ = 171;
v___x_3649_ = lean_uint32_dec_eq(v_curr_3647_, v___x_3648_);
if (v___x_3649_ == 0)
{
lean_object* v___f_3650_; lean_object* v___f_3661_; uint8_t v___y_3663_; uint8_t v___y_3675_; uint8_t v___y_3681_; uint32_t v___x_3690_; uint8_t v___x_3691_; 
v___f_3650_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0));
v___f_3661_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1));
v___x_3690_ = 65;
v___x_3691_ = lean_uint32_dec_le(v___x_3690_, v_curr_3647_);
if (v___x_3691_ == 0)
{
goto v___jp_3685_;
}
else
{
uint32_t v___x_3692_; uint8_t v___x_3693_; 
v___x_3692_ = 90;
v___x_3693_ = lean_uint32_dec_le(v_curr_3647_, v___x_3692_);
if (v___x_3693_ == 0)
{
goto v___jp_3685_;
}
else
{
goto v___jp_3651_;
}
}
v___jp_3651_:
{
lean_object* v_idPart_3652_; lean_object* v_startPos_3653_; lean_object* v_stopPos_3654_; lean_object* v_startPos_3655_; lean_object* v_stopPos_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
lean_inc_ref(v_ss_3633_);
v_idPart_3652_ = lean_substring_takewhile(v_ss_3633_, v___f_3650_);
v_startPos_3653_ = lean_ctor_get(v_idPart_3652_, 1);
lean_inc(v_startPos_3653_);
v_stopPos_3654_ = lean_ctor_get(v_idPart_3652_, 2);
lean_inc(v_stopPos_3654_);
v_startPos_3655_ = lean_ctor_get(v_ss_3633_, 1);
v_stopPos_3656_ = lean_ctor_get(v_ss_3633_, 2);
v___x_3657_ = lean_nat_sub(v_stopPos_3654_, v_startPos_3653_);
lean_dec(v_startPos_3653_);
lean_dec(v_stopPos_3654_);
v___x_3658_ = lean_nat_sub(v_stopPos_3656_, v_startPos_3655_);
v___x_3659_ = lean_substring_extract(v_ss_3633_, v___x_3657_, v___x_3658_);
v___x_3660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3660_, 0, v_idPart_3652_);
lean_ctor_set(v___x_3660_, 1, v_acc_3634_);
v_ss_3636_ = v___x_3659_;
v_acc_3637_ = v___x_3660_;
goto v___jp_3635_;
}
v___jp_3662_:
{
if (v___y_3663_ == 0)
{
lean_object* v___x_3664_; 
lean_dec(v_acc_3634_);
lean_dec_ref(v_ss_3633_);
v___x_3664_ = lean_box(0);
return v___x_3664_;
}
else
{
lean_object* v_idPart_3665_; lean_object* v_startPos_3666_; lean_object* v_stopPos_3667_; lean_object* v_startPos_3668_; lean_object* v_stopPos_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
lean_inc_ref(v_ss_3633_);
v_idPart_3665_ = lean_substring_takewhile(v_ss_3633_, v___f_3661_);
v_startPos_3666_ = lean_ctor_get(v_idPart_3665_, 1);
lean_inc(v_startPos_3666_);
v_stopPos_3667_ = lean_ctor_get(v_idPart_3665_, 2);
lean_inc(v_stopPos_3667_);
v_startPos_3668_ = lean_ctor_get(v_ss_3633_, 1);
v_stopPos_3669_ = lean_ctor_get(v_ss_3633_, 2);
v___x_3670_ = lean_nat_sub(v_stopPos_3667_, v_startPos_3666_);
lean_dec(v_startPos_3666_);
lean_dec(v_stopPos_3667_);
v___x_3671_ = lean_nat_sub(v_stopPos_3669_, v_startPos_3668_);
v___x_3672_ = lean_substring_extract(v_ss_3633_, v___x_3670_, v___x_3671_);
v___x_3673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3673_, 0, v_idPart_3665_);
lean_ctor_set(v___x_3673_, 1, v_acc_3634_);
v_ss_3636_ = v___x_3672_;
v_acc_3637_ = v___x_3673_;
goto v___jp_3635_;
}
}
v___jp_3674_:
{
if (v___y_3675_ == 0)
{
uint32_t v___x_3676_; uint8_t v___x_3677_; 
v___x_3676_ = 48;
v___x_3677_ = lean_uint32_dec_le(v___x_3676_, v_curr_3647_);
if (v___x_3677_ == 0)
{
v___y_3663_ = v___x_3677_;
goto v___jp_3662_;
}
else
{
uint32_t v___x_3678_; uint8_t v___x_3679_; 
v___x_3678_ = 57;
v___x_3679_ = lean_uint32_dec_le(v_curr_3647_, v___x_3678_);
v___y_3663_ = v___x_3679_;
goto v___jp_3662_;
}
}
else
{
goto v___jp_3651_;
}
}
v___jp_3680_:
{
if (v___y_3681_ == 0)
{
uint32_t v___x_3682_; uint8_t v___x_3683_; 
v___x_3682_ = 95;
v___x_3683_ = lean_uint32_dec_eq(v_curr_3647_, v___x_3682_);
if (v___x_3683_ == 0)
{
uint8_t v___x_3684_; 
v___x_3684_ = l_Lean_isLetterLike(v_curr_3647_);
v___y_3675_ = v___x_3684_;
goto v___jp_3674_;
}
else
{
v___y_3675_ = v___x_3683_;
goto v___jp_3674_;
}
}
else
{
goto v___jp_3651_;
}
}
v___jp_3685_:
{
uint32_t v___x_3686_; uint8_t v___x_3687_; 
v___x_3686_ = 97;
v___x_3687_ = lean_uint32_dec_le(v___x_3686_, v_curr_3647_);
if (v___x_3687_ == 0)
{
v___y_3681_ = v___x_3687_;
goto v___jp_3680_;
}
else
{
uint32_t v___x_3688_; uint8_t v___x_3689_; 
v___x_3688_ = 122;
v___x_3689_ = lean_uint32_dec_le(v_curr_3647_, v___x_3688_);
v___y_3681_ = v___x_3689_;
goto v___jp_3680_;
}
}
}
else
{
lean_object* v___f_3694_; lean_object* v_escapedPart_3695_; lean_object* v_str_3696_; lean_object* v_startPos_3697_; lean_object* v_stopPos_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3719_; 
v___f_3694_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__2));
lean_inc_ref(v_ss_3633_);
v_escapedPart_3695_ = lean_substring_takewhile(v_ss_3633_, v___f_3694_);
v_str_3696_ = lean_ctor_get(v_escapedPart_3695_, 0);
v_startPos_3697_ = lean_ctor_get(v_escapedPart_3695_, 1);
v_stopPos_3698_ = lean_ctor_get(v_escapedPart_3695_, 2);
v_isSharedCheck_3719_ = !lean_is_exclusive(v_escapedPart_3695_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3700_ = v_escapedPart_3695_;
v_isShared_3701_ = v_isSharedCheck_3719_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_stopPos_3698_);
lean_inc(v_startPos_3697_);
lean_inc(v_str_3696_);
lean_dec(v_escapedPart_3695_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3719_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v_startPos_3702_; lean_object* v_stopPos_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v_escapedPart_3707_; 
v_startPos_3702_ = lean_ctor_get(v_ss_3633_, 1);
v_stopPos_3703_ = lean_ctor_get(v_ss_3633_, 2);
v___x_3704_ = lean_string_utf8_next(v_str_3696_, v_stopPos_3698_);
lean_dec(v_stopPos_3698_);
lean_inc(v_stopPos_3703_);
v___x_3705_ = lean_string_pos_min(v_stopPos_3703_, v___x_3704_);
lean_inc(v___x_3705_);
lean_inc(v_startPos_3697_);
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 2, v___x_3705_);
v_escapedPart_3707_ = v___x_3700_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_str_3696_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_startPos_3697_);
lean_ctor_set(v_reuseFailAlloc_3718_, 2, v___x_3705_);
v_escapedPart_3707_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; uint32_t v___x_3710_; uint32_t v___x_3711_; uint8_t v___x_3712_; uint8_t v___x_3713_; 
v___x_3708_ = lean_nat_sub(v___x_3705_, v_startPos_3697_);
lean_dec(v_startPos_3697_);
lean_dec(v___x_3705_);
lean_inc(v___x_3708_);
lean_inc_ref_n(v_escapedPart_3707_, 2);
v___x_3709_ = lean_substring_prev(v_escapedPart_3707_, v___x_3708_);
v___x_3710_ = lean_substring_get(v_escapedPart_3707_, v___x_3709_);
v___x_3711_ = 187;
v___x_3712_ = lean_uint32_dec_eq(v___x_3710_, v___x_3711_);
v___x_3713_ = lean_bool_not(v___x_3712_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3714_ = lean_nat_sub(v_stopPos_3703_, v_startPos_3702_);
v___x_3715_ = lean_substring_extract(v_ss_3633_, v___x_3708_, v___x_3714_);
v___x_3716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3716_, 0, v_escapedPart_3707_);
lean_ctor_set(v___x_3716_, 1, v_acc_3634_);
v_ss_3636_ = v___x_3715_;
v_acc_3637_ = v___x_3716_;
goto v___jp_3635_;
}
else
{
lean_object* v___x_3717_; 
lean_dec(v___x_3708_);
lean_dec_ref(v_escapedPart_3707_);
lean_dec(v_acc_3634_);
lean_dec_ref(v_ss_3633_);
v___x_3717_ = lean_box(0);
return v___x_3717_;
}
}
}
}
}
else
{
lean_object* v___x_3720_; 
lean_dec(v_acc_3634_);
lean_dec_ref(v_ss_3633_);
v___x_3720_ = lean_box(0);
return v___x_3720_;
}
v___jp_3635_:
{
uint32_t v___x_3638_; uint32_t v___x_3639_; uint8_t v___x_3640_; 
lean_inc_ref(v_ss_3636_);
v___x_3638_ = lean_substring_front(v_ss_3636_);
v___x_3639_ = 46;
v___x_3640_ = lean_uint32_dec_eq(v___x_3638_, v___x_3639_);
if (v___x_3640_ == 0)
{
uint8_t v___x_3641_; 
v___x_3641_ = lean_substring_isempty(v_ss_3636_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; 
lean_dec(v_acc_3637_);
v___x_3642_ = lean_box(0);
return v___x_3642_;
}
else
{
return v_acc_3637_;
}
}
else
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = lean_unsigned_to_nat(1u);
v___x_3644_ = lean_substring_drop(v_ss_3636_, v___x_3643_);
v_ss_3633_ = v___x_3644_;
v_acc_3634_ = v_acc_3637_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* v_ss_3721_){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3722_ = lean_box(0);
v___x_3723_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_ss_3721_, v___x_3722_);
v___x_3724_ = l_List_reverse___redArg(v___x_3723_);
return v___x_3724_;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3728_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3729_ = lean_unsigned_to_nat(10u);
v___x_3730_ = lean_unsigned_to_nat(1236u);
v___x_3731_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3732_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3733_ = l_mkPanicMessageWithDecl(v___x_3732_, v___x_3731_, v___x_3730_, v___x_3729_, v___x_3728_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object* v_init_3734_, lean_object* v_x_3735_){
_start:
{
if (lean_obj_tag(v_x_3735_) == 0)
{
lean_inc(v_init_3734_);
return v_init_3734_;
}
else
{
lean_object* v_head_3736_; lean_object* v_tail_3737_; lean_object* v___x_3738_; lean_object* v_comp_3739_; uint8_t v___y_3741_; uint32_t v___x_3748_; uint32_t v___x_3749_; uint8_t v___x_3750_; 
v_head_3736_ = lean_ctor_get(v_x_3735_, 0);
lean_inc(v_head_3736_);
v_tail_3737_ = lean_ctor_get(v_x_3735_, 1);
lean_inc(v_tail_3737_);
lean_dec_ref_known(v_x_3735_, 2);
v___x_3738_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3734_, v_tail_3737_);
v_comp_3739_ = lean_substring_tostring(v_head_3736_);
lean_inc_ref(v_comp_3739_);
v___x_3748_ = lean_string_front(v_comp_3739_);
v___x_3749_ = 171;
v___x_3750_ = lean_uint32_dec_eq(v___x_3748_, v___x_3749_);
if (v___x_3750_ == 0)
{
uint32_t v___x_3751_; uint8_t v___x_3752_; 
v___x_3751_ = 48;
v___x_3752_ = lean_uint32_dec_le(v___x_3751_, v___x_3748_);
if (v___x_3752_ == 0)
{
v___y_3741_ = v___x_3752_;
goto v___jp_3740_;
}
else
{
uint32_t v___x_3753_; uint8_t v___x_3754_; 
v___x_3753_ = 57;
v___x_3754_ = lean_uint32_dec_le(v___x_3748_, v___x_3753_);
v___y_3741_ = v___x_3754_;
goto v___jp_3740_;
}
}
else
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3755_ = lean_unsigned_to_nat(1u);
v___x_3756_ = lean_string_drop(v_comp_3739_, v___x_3755_);
v___x_3757_ = lean_string_dropright(v___x_3756_, v___x_3755_);
v___x_3758_ = l_Lean_Name_str___override(v___x_3738_, v___x_3757_);
return v___x_3758_;
}
v___jp_3740_:
{
if (v___y_3741_ == 0)
{
lean_object* v___x_3742_; 
v___x_3742_ = l_Lean_Name_str___override(v___x_3738_, v_comp_3739_);
return v___x_3742_;
}
else
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3739_);
lean_dec_ref(v_comp_3739_);
if (lean_obj_tag(v___x_3743_) == 1)
{
lean_object* v_val_3744_; lean_object* v___x_3745_; 
v_val_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc(v_val_3744_);
lean_dec_ref_known(v___x_3743_, 1);
v___x_3745_ = l_Lean_Name_num___override(v___x_3738_, v_val_3744_);
return v___x_3745_;
}
else
{
lean_object* v___x_3746_; lean_object* v___x_3747_; 
lean_dec(v___x_3743_);
lean_dec(v___x_3738_);
v___x_3746_ = lean_obj_once(&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3, &l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3747_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3746_);
return v___x_3747_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_init_3759_, lean_object* v_x_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3759_, v_x_3760_);
lean_dec(v_init_3759_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3762_){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = lean_box(0);
v___x_3764_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3762_, v___x_3763_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v___x_3765_; 
v___x_3765_ = lean_box(0);
return v___x_3765_;
}
else
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3766_ = lean_box(0);
v___x_3767_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v___x_3766_, v___x_3764_);
return v___x_3767_;
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3768_){
_start:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3769_ = lean_unsigned_to_nat(0u);
v___x_3770_ = lean_string_utf8_byte_size(v_s_3768_);
v___x_3771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3771_, 0, v_s_3768_);
lean_ctor_set(v___x_3771_, 1, v___x_3769_);
lean_ctor_set(v___x_3771_, 2, v___x_3770_);
v___x_3772_ = l_Substring_Raw_toName(v___x_3771_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3773_){
_start:
{
lean_object* v___x_3774_; uint32_t v___x_3775_; uint32_t v___x_3776_; uint8_t v___x_3777_; 
v___x_3774_ = lean_unsigned_to_nat(0u);
v___x_3775_ = lean_string_utf8_get(v_s_3773_, v___x_3774_);
v___x_3776_ = 96;
v___x_3777_ = lean_uint32_dec_eq(v___x_3775_, v___x_3776_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; 
lean_dec_ref(v_s_3773_);
v___x_3778_ = lean_box(0);
return v___x_3778_;
}
else
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3779_ = lean_string_utf8_byte_size(v_s_3773_);
v___x_3780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3780_, 0, v_s_3773_);
lean_ctor_set(v___x_3780_, 1, v___x_3774_);
lean_ctor_set(v___x_3780_, 2, v___x_3779_);
v___x_3781_ = lean_unsigned_to_nat(1u);
v___x_3782_ = lean_substring_drop(v___x_3780_, v___x_3781_);
v___x_3783_ = l_Substring_Raw_toName(v___x_3782_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v___x_3784_; 
v___x_3784_ = lean_box(0);
return v___x_3784_;
}
else
{
lean_object* v___x_3785_; 
v___x_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3783_);
return v___x_3785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3786_){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3787_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3788_ = l_Lean_Syntax_isLit_x3f(v___x_3787_, v_stx_3786_);
if (lean_obj_tag(v___x_3788_) == 1)
{
lean_object* v_val_3789_; lean_object* v___x_3790_; 
v_val_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_val_3789_);
lean_dec_ref_known(v___x_3788_, 1);
v___x_3790_ = l_Lean_Syntax_decodeNameLit(v_val_3789_);
return v___x_3790_;
}
else
{
lean_object* v___x_3791_; 
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
return v___x_3791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3792_);
lean_dec(v_stx_3792_);
return v_res_3793_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3794_){
_start:
{
if (lean_obj_tag(v_x_3794_) == 1)
{
lean_object* v_args_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; 
v_args_3795_ = lean_ctor_get(v_x_3794_, 2);
v___x_3796_ = lean_unsigned_to_nat(0u);
v___x_3797_ = lean_array_get_size(v_args_3795_);
v___x_3798_ = lean_nat_dec_lt(v___x_3796_, v___x_3797_);
return v___x_3798_;
}
else
{
uint8_t v___x_3799_; 
v___x_3799_ = 0;
return v___x_3799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3800_){
_start:
{
uint8_t v_res_3801_; lean_object* v_r_3802_; 
v_res_3801_ = l_Lean_Syntax_hasArgs(v_x_3800_);
lean_dec(v_x_3800_);
v_r_3802_ = lean_box(v_res_3801_);
return v_r_3802_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3803_){
_start:
{
if (lean_obj_tag(v_x_3803_) == 2)
{
uint8_t v___x_3804_; 
v___x_3804_ = 1;
return v___x_3804_;
}
else
{
uint8_t v___x_3805_; 
v___x_3805_ = 0;
return v___x_3805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3806_){
_start:
{
uint8_t v_res_3807_; lean_object* v_r_3808_; 
v_res_3807_ = l_Lean_Syntax_isAtom(v_x_3806_);
lean_dec(v_x_3806_);
v_r_3808_ = lean_box(v_res_3807_);
return v_r_3808_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3809_, lean_object* v_x_3810_){
_start:
{
if (lean_obj_tag(v_x_3810_) == 2)
{
lean_object* v_val_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v_val_3811_ = lean_ctor_get(v_x_3810_, 1);
lean_inc_ref(v_val_3811_);
lean_dec_ref_known(v_x_3810_, 2);
v___x_3812_ = lean_string_trim(v_val_3811_);
v___x_3813_ = lean_string_trim(v_token_3809_);
v___x_3814_ = lean_string_dec_eq(v___x_3812_, v___x_3813_);
lean_dec_ref(v___x_3813_);
lean_dec_ref(v___x_3812_);
return v___x_3814_;
}
else
{
uint8_t v___x_3815_; 
lean_dec(v_x_3810_);
lean_dec_ref(v_token_3809_);
v___x_3815_ = 0;
return v___x_3815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3816_, lean_object* v_x_3817_){
_start:
{
uint8_t v_res_3818_; lean_object* v_r_3819_; 
v_res_3818_ = l_Lean_Syntax_isToken(v_token_3816_, v_x_3817_);
v_r_3819_ = lean_box(v_res_3818_);
return v_r_3819_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3820_){
_start:
{
switch(lean_obj_tag(v_stx_3820_))
{
case 1:
{
lean_object* v_kind_3821_; lean_object* v_args_3822_; lean_object* v___x_3823_; uint8_t v___x_3824_; 
v_kind_3821_ = lean_ctor_get(v_stx_3820_, 1);
v_args_3822_ = lean_ctor_get(v_stx_3820_, 2);
v___x_3823_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3824_ = lean_name_eq(v_kind_3821_, v___x_3823_);
if (v___x_3824_ == 0)
{
return v___x_3824_;
}
else
{
lean_object* v___x_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v___x_3825_ = lean_array_get_size(v_args_3822_);
v___x_3826_ = lean_unsigned_to_nat(0u);
v___x_3827_ = lean_nat_dec_eq(v___x_3825_, v___x_3826_);
return v___x_3827_;
}
}
case 0:
{
uint8_t v___x_3828_; 
v___x_3828_ = 1;
return v___x_3828_;
}
default: 
{
uint8_t v___x_3829_; 
v___x_3829_ = 0;
return v___x_3829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3830_){
_start:
{
uint8_t v_res_3831_; lean_object* v_r_3832_; 
v_res_3831_ = l_Lean_Syntax_isNone(v_stx_3830_);
lean_dec(v_stx_3830_);
v_r_3832_ = lean_box(v_res_3831_);
return v_r_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3833_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l_Lean_Syntax_getOptional_x3f(v_stx_3833_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v___x_3835_; 
v___x_3835_ = lean_box(0);
return v___x_3835_;
}
else
{
lean_object* v_val_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3844_; 
v_val_3836_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3838_ = v___x_3834_;
v_isShared_3839_ = v_isSharedCheck_3844_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_val_3836_);
lean_dec(v___x_3834_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3844_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3840_; lean_object* v___x_3842_; 
v___x_3840_ = l_Lean_Syntax_getId(v_val_3836_);
lean_dec(v_val_3836_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 0, v___x_3840_);
v___x_3842_ = v___x_3838_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3840_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3845_);
lean_dec(v_stx_3845_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3847_, lean_object* v_x_3848_){
_start:
{
if (lean_obj_tag(v_x_3848_) == 1)
{
lean_object* v_args_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; 
v_args_3849_ = lean_ctor_get(v_x_3848_, 2);
lean_inc_ref(v_p_3847_);
lean_inc_ref(v_x_3848_);
v___x_3850_ = lean_apply_1(v_p_3847_, v_x_3848_);
v___x_3851_ = lean_unbox(v___x_3850_);
if (v___x_3851_ == 0)
{
lean_object* v___x_3852_; lean_object* v___x_3853_; size_t v_sz_3854_; size_t v___x_3855_; lean_object* v___x_3856_; lean_object* v_fst_3857_; 
lean_inc_ref(v_args_3849_);
lean_dec_ref_known(v_x_3848_, 3);
v___x_3852_ = lean_box(0);
v___x_3853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3854_ = lean_array_size(v_args_3849_);
v___x_3855_ = ((size_t)0ULL);
v___x_3856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3847_, v_args_3849_, v_sz_3854_, v___x_3855_, v___x_3853_);
lean_dec_ref(v_args_3849_);
v_fst_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_fst_3857_);
lean_dec_ref(v___x_3856_);
if (lean_obj_tag(v_fst_3857_) == 0)
{
return v___x_3852_;
}
else
{
lean_object* v_val_3858_; 
v_val_3858_ = lean_ctor_get(v_fst_3857_, 0);
lean_inc(v_val_3858_);
lean_dec_ref_known(v_fst_3857_, 1);
return v_val_3858_;
}
}
else
{
lean_object* v___x_3859_; 
lean_dec_ref(v_p_3847_);
v___x_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3859_, 0, v_x_3848_);
return v___x_3859_;
}
}
else
{
lean_object* v___x_3860_; uint8_t v___x_3861_; 
lean_inc(v_x_3848_);
v___x_3860_ = lean_apply_1(v_p_3847_, v_x_3848_);
v___x_3861_ = lean_unbox(v___x_3860_);
if (v___x_3861_ == 0)
{
lean_object* v___x_3862_; 
lean_dec(v_x_3848_);
v___x_3862_ = lean_box(0);
return v___x_3862_;
}
else
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3863_, 0, v_x_3848_);
return v___x_3863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3864_, lean_object* v_as_3865_, size_t v_sz_3866_, size_t v_i_3867_, lean_object* v_b_3868_){
_start:
{
uint8_t v___x_3869_; 
v___x_3869_ = lean_usize_dec_lt(v_i_3867_, v_sz_3866_);
if (v___x_3869_ == 0)
{
lean_dec_ref(v_p_3864_);
lean_inc_ref(v_b_3868_);
return v_b_3868_;
}
else
{
lean_object* v___x_3870_; lean_object* v_a_3871_; lean_object* v___x_3872_; 
v___x_3870_ = lean_box(0);
v_a_3871_ = lean_array_uget_borrowed(v_as_3865_, v_i_3867_);
lean_inc(v_a_3871_);
lean_inc_ref(v_p_3864_);
v___x_3872_ = l_Lean_Syntax_findAux(v_p_3864_, v_a_3871_);
if (lean_obj_tag(v___x_3872_) == 1)
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
lean_dec_ref(v_p_3864_);
v___x_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3872_);
v___x_3874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
lean_ctor_set(v___x_3874_, 1, v___x_3870_);
return v___x_3874_;
}
else
{
lean_object* v___x_3875_; size_t v___x_3876_; size_t v___x_3877_; 
lean_dec(v___x_3872_);
v___x_3875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3876_ = ((size_t)1ULL);
v___x_3877_ = lean_usize_add(v_i_3867_, v___x_3876_);
v_i_3867_ = v___x_3877_;
v_b_3868_ = v___x_3875_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3879_, lean_object* v_as_3880_, lean_object* v_sz_3881_, lean_object* v_i_3882_, lean_object* v_b_3883_){
_start:
{
size_t v_sz_boxed_3884_; size_t v_i_boxed_3885_; lean_object* v_res_3886_; 
v_sz_boxed_3884_ = lean_unbox_usize(v_sz_3881_);
lean_dec(v_sz_3881_);
v_i_boxed_3885_ = lean_unbox_usize(v_i_3882_);
lean_dec(v_i_3882_);
v_res_3886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3879_, v_as_3880_, v_sz_boxed_3884_, v_i_boxed_3885_, v_b_3883_);
lean_dec_ref(v_b_3883_);
lean_dec_ref(v_as_3880_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3887_, lean_object* v_p_3888_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_Syntax_findAux(v_p_3888_, v_stx_3887_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3890_){
_start:
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Lean_Syntax_isNatLit_x3f(v_s_3890_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v___x_3892_; 
v___x_3892_ = lean_unsigned_to_nat(0u);
return v___x_3892_;
}
else
{
lean_object* v_val_3893_; 
v_val_3893_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_val_3893_);
lean_dec_ref_known(v___x_3891_, 1);
return v_val_3893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l_Lean_TSyntax_getNat(v_s_3894_);
lean_dec(v_s_3894_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3899_){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3901_ = l_Lean_Syntax_isLit_x3f(v___x_3900_, v_stx_3899_);
if (lean_obj_tag(v___x_3901_) == 1)
{
lean_object* v_val_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v_val_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_val_3902_);
lean_dec_ref_known(v___x_3901_, 1);
v___x_3903_ = lean_unsigned_to_nat(0u);
v___x_3904_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3902_, v___x_3903_, v___x_3903_);
lean_dec(v_val_3902_);
return v___x_3904_;
}
else
{
lean_object* v___x_3905_; 
lean_dec(v___x_3901_);
v___x_3905_ = lean_box(0);
return v___x_3905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3906_);
lean_dec(v_stx_3906_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3908_){
_start:
{
lean_object* v___x_3909_; 
v___x_3909_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3908_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v___x_3910_; 
v___x_3910_ = lean_unsigned_to_nat(0u);
return v___x_3910_;
}
else
{
lean_object* v_val_3911_; 
v_val_3911_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_val_3911_);
lean_dec_ref_known(v___x_3909_, 1);
return v_val_3911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Lean_TSyntax_getHexNumVal(v_s_3912_);
lean_dec(v_s_3912_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3914_, lean_object* v_p_3915_, lean_object* v_n_3916_){
_start:
{
uint8_t v___x_3917_; 
v___x_3917_ = lean_string_utf8_at_end(v_s_3914_, v_p_3915_);
if (v___x_3917_ == 0)
{
lean_object* v___x_3918_; uint32_t v___x_3919_; uint32_t v___x_3920_; uint8_t v___x_3921_; 
v___x_3918_ = lean_string_utf8_next(v_s_3914_, v_p_3915_);
v___x_3919_ = lean_string_utf8_get(v_s_3914_, v_p_3915_);
lean_dec(v_p_3915_);
v___x_3920_ = 95;
v___x_3921_ = lean_uint32_dec_eq(v___x_3919_, v___x_3920_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = lean_unsigned_to_nat(1u);
v___x_3923_ = lean_nat_add(v_n_3916_, v___x_3922_);
lean_dec(v_n_3916_);
v_p_3915_ = v___x_3918_;
v_n_3916_ = v___x_3923_;
goto _start;
}
else
{
v_p_3915_ = v___x_3918_;
goto _start;
}
}
else
{
lean_dec(v_p_3915_);
return v_n_3916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3926_, lean_object* v_p_3927_, lean_object* v_n_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3926_, v_p_3927_, v_n_3928_);
lean_dec_ref(v_s_3926_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3930_){
_start:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3931_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3932_ = l_Lean_Syntax_isLit_x3f(v___x_3931_, v_s_3930_);
if (lean_obj_tag(v___x_3932_) == 1)
{
lean_object* v_val_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v_val_3933_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_val_3933_);
lean_dec_ref_known(v___x_3932_, 1);
v___x_3934_ = lean_unsigned_to_nat(0u);
v___x_3935_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3933_, v___x_3934_, v___x_3934_);
lean_dec(v_val_3933_);
return v___x_3935_;
}
else
{
lean_object* v___x_3936_; 
lean_dec(v___x_3932_);
v___x_3936_ = lean_unsigned_to_nat(0u);
return v___x_3936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l_Lean_TSyntax_getHexNumSize(v_s_3937_);
lean_dec(v_s_3937_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3939_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l_Lean_Syntax_getId(v_s_3939_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_Lean_TSyntax_getId(v_s_3941_);
lean_dec(v_s_3941_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_3950_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Lean_Syntax_isScientificLit_x3f(v_s_3950_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v___x_3952_; 
v___x_3952_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
return v___x_3952_;
}
else
{
lean_object* v_val_3953_; 
v_val_3953_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_val_3953_);
lean_dec_ref_known(v___x_3951_, 1);
return v_val_3953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_TSyntax_getScientific(v_s_3954_);
lean_dec(v_s_3954_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_3956_){
_start:
{
lean_object* v___x_3957_; 
v___x_3957_ = l_Lean_Syntax_isStrLit_x3f(v_s_3956_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v___x_3958_; 
v___x_3958_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_3958_;
}
else
{
lean_object* v_val_3959_; 
v_val_3959_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_val_3959_);
lean_dec_ref_known(v___x_3957_, 1);
return v_val_3959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_TSyntax_getString(v_s_3960_);
lean_dec(v_s_3960_);
return v_res_3961_;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_3962_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_Lean_Syntax_isCharLit_x3f(v_s_3962_);
if (lean_obj_tag(v___x_3963_) == 0)
{
uint32_t v___x_3964_; 
v___x_3964_ = 65;
return v___x_3964_;
}
else
{
lean_object* v_val_3965_; uint32_t v___x_3966_; 
v_val_3965_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_val_3965_);
lean_dec_ref_known(v___x_3963_, 1);
v___x_3966_ = lean_unbox_uint32(v_val_3965_);
lean_dec(v_val_3965_);
return v___x_3966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_3967_){
_start:
{
uint32_t v_res_3968_; lean_object* v_r_3969_; 
v_res_3968_ = l_Lean_TSyntax_getChar(v_s_3967_);
lean_dec(v_s_3967_);
v_r_3969_ = lean_box_uint32(v_res_3968_);
return v_r_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_3970_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Lean_Syntax_isNameLit_x3f(v_s_3970_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v___x_3972_; 
v___x_3972_ = lean_box(0);
return v___x_3972_;
}
else
{
lean_object* v_val_3973_; 
v_val_3973_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_val_3973_);
lean_dec_ref_known(v___x_3971_, 1);
return v_val_3973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_TSyntax_getName(v_s_3974_);
lean_dec(v_s_3974_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_3976_){
_start:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3977_ = lean_unsigned_to_nat(0u);
v___x_3978_ = l_Lean_Syntax_getArg(v_s_3976_, v___x_3977_);
v___x_3979_ = l_Lean_Syntax_getId(v___x_3978_);
lean_dec(v___x_3978_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Lean_TSyntax_getHygieneInfo(v_s_3980_);
lean_dec(v_s_3980_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_3982_, lean_object* v_a_3983_){
_start:
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Lean_Syntax_SepArray_ofElems(v_sep_3982_, v_a_3983_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_3985_, v_a_3986_);
lean_dec_ref(v_a_3986_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_3988_){
_start:
{
lean_object* v___f_3989_; 
v___f_3989_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3989_, 0, v_sep_3988_);
return v___f_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_3990_, lean_object* v_sep_3991_){
_start:
{
lean_object* v___f_3992_; 
v___f_3992_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3992_, 0, v_sep_3991_);
return v___f_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_3993_, lean_object* v_sep_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_3993_, v_sep_3994_);
lean_dec(v_k_3993_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_3996_, lean_object* v_val_3997_, uint8_t v_canonical_3998_){
_start:
{
lean_object* v___x_3999_; lean_object* v_src_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v_imported_4003_; lean_object* v_ctx_4004_; lean_object* v_scopes_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4021_; 
v___x_3999_ = lean_unsigned_to_nat(0u);
v_src_4000_ = l_Lean_Syntax_getArg(v_s_3996_, v___x_3999_);
v___x_4001_ = l_Lean_Syntax_getId(v_src_4000_);
v___x_4002_ = l_Lean_extractMacroScopes(v___x_4001_);
v_imported_4003_ = lean_ctor_get(v___x_4002_, 1);
v_ctx_4004_ = lean_ctor_get(v___x_4002_, 2);
v_scopes_4005_ = lean_ctor_get(v___x_4002_, 3);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4021_ == 0)
{
lean_object* v_unused_4022_; 
v_unused_4022_ = lean_ctor_get(v___x_4002_, 0);
lean_dec(v_unused_4022_);
v___x_4007_ = v___x_4002_;
v_isShared_4008_ = v_isSharedCheck_4021_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_scopes_4005_);
lean_inc(v_ctx_4004_);
lean_inc(v_imported_4003_);
lean_dec(v___x_4002_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4021_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4009_; lean_object* v___x_4011_; 
v___x_4009_ = l_Lean_Name_eraseMacroScopes(v_val_3997_);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v___x_4009_);
v___x_4011_ = v___x_4007_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v___x_4009_);
lean_ctor_set(v_reuseFailAlloc_4020_, 1, v_imported_4003_);
lean_ctor_set(v_reuseFailAlloc_4020_, 2, v_ctx_4004_);
lean_ctor_set(v_reuseFailAlloc_4020_, 3, v_scopes_4005_);
v___x_4011_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
lean_object* v_id_4012_; lean_object* v___x_4013_; uint8_t v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v_id_4012_ = l_Lean_MacroScopesView_review(v___x_4011_);
v___x_4013_ = l_Lean_SourceInfo_fromRef(v_src_4000_, v_canonical_3998_);
lean_dec(v_src_4000_);
v___x_4014_ = 1;
v___x_4015_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_3997_, v___x_4014_);
v___x_4016_ = lean_string_utf8_byte_size(v___x_4015_);
v___x_4017_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4015_);
lean_ctor_set(v___x_4017_, 1, v___x_3999_);
lean_ctor_set(v___x_4017_, 2, v___x_4016_);
v___x_4018_ = lean_box(0);
v___x_4019_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4013_);
lean_ctor_set(v___x_4019_, 1, v___x_4017_);
lean_ctor_set(v___x_4019_, 2, v_id_4012_);
lean_ctor_set(v___x_4019_, 3, v___x_4018_);
return v___x_4019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_4023_, lean_object* v_val_4024_, lean_object* v_canonical_4025_){
_start:
{
uint8_t v_canonical_boxed_4026_; lean_object* v_res_4027_; 
v_canonical_boxed_4026_ = lean_unbox(v_canonical_4025_);
v_res_4027_ = l_Lean_HygieneInfo_mkIdent(v_s_4023_, v_val_4024_, v_canonical_boxed_4026_);
lean_dec(v_s_4023_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_4028_, lean_object* v_inst_4029_, lean_object* v_a_4030_){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = lean_apply_1(v_inst_4028_, v_a_4030_);
v___x_4032_ = lean_apply_1(v_inst_4029_, v___x_4031_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_4033_, lean_object* v_inst_4034_){
_start:
{
lean_object* v___f_4035_; 
v___f_4035_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4035_, 0, v_inst_4033_);
lean_closure_set(v___f_4035_, 1, v_inst_4034_);
return v___f_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_4036_, lean_object* v_k_4037_, lean_object* v_k_x27_4038_, lean_object* v_inst_4039_, lean_object* v_inst_4040_){
_start:
{
lean_object* v___f_4041_; 
v___f_4041_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4041_, 0, v_inst_4039_);
lean_closure_set(v___f_4041_, 1, v_inst_4040_);
return v___f_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_4042_, lean_object* v_k_4043_, lean_object* v_k_x27_4044_, lean_object* v_inst_4045_, lean_object* v_inst_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_4042_, v_k_4043_, v_k_x27_4044_, v_inst_4045_, v_inst_4046_);
lean_dec(v_k_x27_4044_);
lean_dec(v_k_4043_);
return v_res_4047_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4055_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4056_ = l_Lean_mkCIdent(v___x_4055_);
return v___x_4056_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4062_ = l_Lean_mkCIdent(v___x_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4063_){
_start:
{
if (v_x_4063_ == 0)
{
lean_object* v___x_4064_; 
v___x_4064_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4064_;
}
else
{
lean_object* v___x_4065_; 
v___x_4065_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4066_){
_start:
{
uint8_t v_x_85__boxed_4067_; lean_object* v_res_4068_; 
v_x_85__boxed_4067_ = lean_unbox(v_x_4066_);
v_res_4068_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4067_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4071_){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = lean_box(2);
v___x_4073_ = l_Lean_Syntax_mkCharLit(v_val_4071_, v___x_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4074_){
_start:
{
uint32_t v_val_boxed_4075_; lean_object* v_res_4076_; 
v_val_boxed_4075_ = lean_unbox_uint32(v_val_4074_);
lean_dec(v_val_4074_);
v_res_4076_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4075_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4079_){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4080_ = lean_box(2);
v___x_4081_ = l_Lean_Syntax_mkStrLit(v_val_4079_, v___x_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4084_){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4085_ = l_Nat_reprFast(v_n_4084_);
v___x_4086_ = lean_box(2);
v___x_4087_ = l_Lean_Syntax_mkNumLit(v___x_4085_, v___x_4086_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4095_){
_start:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4096_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4097_ = lean_substring_tostring(v_s_4095_);
v___x_4098_ = lean_box(2);
v___x_4099_ = l_Lean_Syntax_mkStrLit(v___x_4097_, v___x_4098_);
v___x_4100_ = lean_unsigned_to_nat(1u);
v___x_4101_ = lean_mk_empty_array_with_capacity(v___x_4100_);
v___x_4102_ = lean_array_push(v___x_4101_, v___x_4099_);
v___x_4103_ = l_Lean_Syntax_mkCApp(v___x_4096_, v___x_4102_);
return v___x_4103_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f___closed__0(void){
_start:
{
uint8_t v___x_4106_; uint8_t v___x_4107_; 
v___x_4106_ = 0;
v___x_4107_ = lean_bool_not(v___x_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4108_, lean_object* v_x_4109_){
_start:
{
switch(lean_obj_tag(v_x_4109_))
{
case 0:
{
uint8_t v___x_4110_; 
v___x_4110_ = l_List_isEmpty___redArg(v_acc_4108_);
if (v___x_4110_ == 0)
{
lean_object* v___x_4111_; 
v___x_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4111_, 0, v_acc_4108_);
return v___x_4111_;
}
else
{
lean_object* v___x_4112_; 
lean_dec(v_acc_4108_);
v___x_4112_ = lean_box(0);
return v___x_4112_;
}
}
case 1:
{
lean_object* v_pre_4113_; lean_object* v_str_4114_; lean_object* v_val_4116_; lean_object* v___x_4119_; lean_object* v___x_4120_; uint8_t v___x_4121_; 
v_pre_4113_ = lean_ctor_get(v_x_4109_, 0);
lean_inc(v_pre_4113_);
v_str_4114_ = lean_ctor_get(v_x_4109_, 1);
lean_inc_ref(v_str_4114_);
lean_dec_ref_known(v_x_4109_, 2);
v___x_4119_ = lean_unsigned_to_nat(0u);
v___x_4120_ = lean_string_utf8_byte_size(v_str_4114_);
v___x_4121_ = lean_nat_dec_lt(v___x_4119_, v___x_4120_);
if (v___x_4121_ == 0)
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4122_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4123_ = lean_string_append(v___x_4122_, v_str_4114_);
lean_dec_ref(v_str_4114_);
v___x_4124_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4125_ = lean_string_append(v___x_4123_, v___x_4124_);
v_val_4116_ = v___x_4125_;
goto v___jp_4115_;
}
else
{
lean_object* v___f_4126_; uint8_t v___y_4135_; uint8_t v___x_4136_; 
v___f_4126_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v___x_4136_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f___closed__0, &l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f___closed__0);
if (v___x_4136_ == 0)
{
v___y_4135_ = v___x_4136_;
goto v___jp_4134_;
}
else
{
lean_object* v___f_4137_; uint8_t v___y_4144_; uint32_t v___y_4146_; uint8_t v___y_4147_; uint32_t v___y_4152_; uint8_t v___y_4158_; uint8_t v_c_4167_; uint8_t v___y_4169_; uint8_t v___y_4173_; uint8_t v___x_4178_; uint8_t v___x_4179_; 
v___f_4137_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_4167_ = lean_string_get_byte_fast(v_str_4114_, v___x_4119_);
v___x_4178_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_4179_ = lean_uint8_dec_le(v___x_4178_, v_c_4167_);
if (v___x_4179_ == 0)
{
v___y_4173_ = v___x_4179_;
goto v___jp_4172_;
}
else
{
uint8_t v___x_4180_; uint8_t v___x_4181_; 
v___x_4180_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_4181_ = lean_uint8_dec_le(v_c_4167_, v___x_4180_);
v___y_4173_ = v___x_4181_;
goto v___jp_4172_;
}
v___jp_4138_:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; uint8_t v___x_4142_; 
lean_inc_ref(v_str_4114_);
v___x_4139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4139_, 0, v_str_4114_);
lean_ctor_set(v___x_4139_, 1, v___x_4119_);
lean_ctor_set(v___x_4139_, 2, v___x_4120_);
v___x_4140_ = lean_unsigned_to_nat(1u);
v___x_4141_ = lean_substring_drop(v___x_4139_, v___x_4140_);
v___x_4142_ = lean_substring_all(v___x_4141_, v___f_4137_);
v___y_4135_ = v___x_4142_;
goto v___jp_4134_;
}
v___jp_4143_:
{
if (v___y_4144_ == 0)
{
goto v___jp_4127_;
}
else
{
goto v___jp_4138_;
}
}
v___jp_4145_:
{
if (v___y_4147_ == 0)
{
uint32_t v___x_4148_; uint8_t v___x_4149_; 
v___x_4148_ = 95;
v___x_4149_ = lean_uint32_dec_eq(v___y_4146_, v___x_4148_);
if (v___x_4149_ == 0)
{
uint8_t v___x_4150_; 
v___x_4150_ = l_Lean_isLetterLike(v___y_4146_);
v___y_4144_ = v___x_4150_;
goto v___jp_4143_;
}
else
{
v___y_4144_ = v___x_4149_;
goto v___jp_4143_;
}
}
else
{
goto v___jp_4138_;
}
}
v___jp_4151_:
{
uint32_t v___x_4153_; uint8_t v___x_4154_; 
v___x_4153_ = 97;
v___x_4154_ = lean_uint32_dec_le(v___x_4153_, v___y_4152_);
if (v___x_4154_ == 0)
{
v___y_4146_ = v___y_4152_;
v___y_4147_ = v___x_4154_;
goto v___jp_4145_;
}
else
{
uint32_t v___x_4155_; uint8_t v___x_4156_; 
v___x_4155_ = 122;
v___x_4156_ = lean_uint32_dec_le(v___y_4152_, v___x_4155_);
v___y_4146_ = v___y_4152_;
v___y_4147_ = v___x_4156_;
goto v___jp_4145_;
}
}
v___jp_4157_:
{
if (v___y_4158_ == 0)
{
uint32_t v___x_4159_; uint32_t v___x_4160_; uint8_t v___x_4161_; 
v___x_4159_ = lean_string_utf8_get(v_str_4114_, v___x_4119_);
v___x_4160_ = 65;
v___x_4161_ = lean_uint32_dec_le(v___x_4160_, v___x_4159_);
if (v___x_4161_ == 0)
{
v___y_4152_ = v___x_4159_;
goto v___jp_4151_;
}
else
{
uint32_t v___x_4162_; uint8_t v___x_4163_; 
v___x_4162_ = 90;
v___x_4163_ = lean_uint32_dec_le(v___x_4159_, v___x_4162_);
if (v___x_4163_ == 0)
{
v___y_4152_ = v___x_4159_;
goto v___jp_4151_;
}
else
{
goto v___jp_4138_;
}
}
}
else
{
v_val_4116_ = v_str_4114_;
goto v___jp_4115_;
}
}
v___jp_4164_:
{
lean_object* v___x_4165_; uint8_t v___x_4166_; 
v___x_4165_ = lean_unsigned_to_nat(1u);
v___x_4166_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4114_, v___x_4165_);
v___y_4158_ = v___x_4166_;
goto v___jp_4157_;
}
v___jp_4168_:
{
if (v___y_4169_ == 0)
{
uint8_t v___x_4170_; uint8_t v___x_4171_; 
v___x_4170_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_4171_ = lean_uint8_dec_eq(v_c_4167_, v___x_4170_);
if (v___x_4171_ == 0)
{
v___y_4158_ = v___x_4171_;
goto v___jp_4157_;
}
else
{
goto v___jp_4164_;
}
}
else
{
goto v___jp_4164_;
}
}
v___jp_4172_:
{
if (v___y_4173_ == 0)
{
uint8_t v___x_4174_; uint8_t v___x_4175_; 
v___x_4174_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_4175_ = lean_uint8_dec_le(v___x_4174_, v_c_4167_);
if (v___x_4175_ == 0)
{
v___y_4169_ = v___x_4175_;
goto v___jp_4168_;
}
else
{
uint8_t v___x_4176_; uint8_t v___x_4177_; 
v___x_4176_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_4177_ = lean_uint8_dec_le(v_c_4167_, v___x_4176_);
v___y_4169_ = v___x_4177_;
goto v___jp_4168_;
}
}
else
{
goto v___jp_4164_;
}
}
}
v___jp_4127_:
{
uint8_t v___x_4128_; 
lean_inc_ref(v_str_4114_);
v___x_4128_ = lean_string_any(v_str_4114_, v___f_4126_);
if (v___x_4128_ == 0)
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4129_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4130_ = lean_string_append(v___x_4129_, v_str_4114_);
lean_dec_ref(v_str_4114_);
v___x_4131_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4132_ = lean_string_append(v___x_4130_, v___x_4131_);
v_val_4116_ = v___x_4132_;
goto v___jp_4115_;
}
else
{
lean_object* v___x_4133_; 
lean_dec_ref(v_str_4114_);
lean_dec(v_pre_4113_);
lean_dec(v_acc_4108_);
v___x_4133_ = lean_box(0);
return v___x_4133_;
}
}
v___jp_4134_:
{
if (v___y_4135_ == 0)
{
goto v___jp_4127_;
}
else
{
v_val_4116_ = v_str_4114_;
goto v___jp_4115_;
}
}
}
v___jp_4115_:
{
lean_object* v___x_4117_; 
v___x_4117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4117_, 0, v_val_4116_);
lean_ctor_set(v___x_4117_, 1, v_acc_4108_);
v_acc_4108_ = v___x_4117_;
v_x_4109_ = v_pre_4113_;
goto _start;
}
}
default: 
{
lean_object* v___x_4182_; 
lean_dec_ref_known(v_x_4109_, 2);
lean_dec(v_acc_4108_);
v___x_4182_ = lean_box(0);
return v___x_4182_;
}
}
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__3(void){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4189_ = ((lean_object*)(l_Lean_quoteNameMk___closed__2));
v___x_4190_ = l_Lean_mkCIdent(v___x_4189_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object* v_x_4201_){
_start:
{
switch(lean_obj_tag(v_x_4201_))
{
case 0:
{
lean_object* v___x_4202_; 
v___x_4202_ = lean_obj_once(&l_Lean_quoteNameMk___closed__3, &l_Lean_quoteNameMk___closed__3_once, _init_l_Lean_quoteNameMk___closed__3);
return v___x_4202_;
}
case 1:
{
lean_object* v_pre_4203_; lean_object* v_str_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v_pre_4203_ = lean_ctor_get(v_x_4201_, 0);
lean_inc(v_pre_4203_);
v_str_4204_ = lean_ctor_get(v_x_4201_, 1);
lean_inc_ref(v_str_4204_);
lean_dec_ref_known(v_x_4201_, 2);
v___x_4205_ = ((lean_object*)(l_Lean_quoteNameMk___closed__5));
v___x_4206_ = l_Lean_quoteNameMk(v_pre_4203_);
v___x_4207_ = lean_box(2);
v___x_4208_ = l_Lean_Syntax_mkStrLit(v_str_4204_, v___x_4207_);
v___x_4209_ = lean_unsigned_to_nat(2u);
v___x_4210_ = lean_mk_empty_array_with_capacity(v___x_4209_);
v___x_4211_ = lean_array_push(v___x_4210_, v___x_4206_);
v___x_4212_ = lean_array_push(v___x_4211_, v___x_4208_);
v___x_4213_ = l_Lean_Syntax_mkCApp(v___x_4205_, v___x_4212_);
return v___x_4213_;
}
default: 
{
lean_object* v_pre_4214_; lean_object* v_i_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v_pre_4214_ = lean_ctor_get(v_x_4201_, 0);
lean_inc(v_pre_4214_);
v_i_4215_ = lean_ctor_get(v_x_4201_, 1);
lean_inc(v_i_4215_);
lean_dec_ref_known(v_x_4201_, 2);
v___x_4216_ = ((lean_object*)(l_Lean_quoteNameMk___closed__7));
v___x_4217_ = l_Lean_quoteNameMk(v_pre_4214_);
v___x_4218_ = l_Nat_reprFast(v_i_4215_);
v___x_4219_ = lean_box(2);
v___x_4220_ = l_Lean_Syntax_mkNumLit(v___x_4218_, v___x_4219_);
v___x_4221_ = lean_unsigned_to_nat(2u);
v___x_4222_ = lean_mk_empty_array_with_capacity(v___x_4221_);
v___x_4223_ = lean_array_push(v___x_4222_, v___x_4217_);
v___x_4224_ = lean_array_push(v___x_4223_, v___x_4220_);
v___x_4225_ = l_Lean_Syntax_mkCApp(v___x_4216_, v___x_4224_);
return v___x_4225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object* v_n_4232_){
_start:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4233_ = lean_box(0);
lean_inc(v_n_4232_);
v___x_4234_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4233_, v_n_4232_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v___x_4235_; 
v___x_4235_ = l_Lean_quoteNameMk(v_n_4232_);
return v___x_4235_;
}
else
{
lean_object* v_val_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
lean_dec(v_n_4232_);
v_val_4236_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_val_4236_);
lean_dec_ref_known(v___x_4234_, 1);
v___x_4237_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4238_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4239_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4240_ = lean_string_intercalate(v___x_4239_, v_val_4236_);
v___x_4241_ = lean_string_append(v___x_4238_, v___x_4240_);
lean_dec_ref(v___x_4240_);
v___x_4242_ = lean_box(2);
v___x_4243_ = l_Lean_Syntax_mkNameLit(v___x_4241_, v___x_4242_);
v___x_4244_ = lean_unsigned_to_nat(1u);
v___x_4245_ = lean_mk_empty_array_with_capacity(v___x_4244_);
v___x_4246_ = lean_array_push(v___x_4245_, v___x_4243_);
v___x_4247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4242_);
lean_ctor_set(v___x_4247_, 1, v___x_4237_);
lean_ctor_set(v___x_4247_, 2, v___x_4246_);
return v___x_4247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object* v_n_4248_){
_start:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4249_ = lean_box(0);
lean_inc(v_n_4248_);
v___x_4250_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4249_, v_n_4248_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v___x_4251_; 
v___x_4251_ = l_Lean_quoteNameMk(v_n_4248_);
return v___x_4251_;
}
else
{
lean_object* v_val_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
lean_dec(v_n_4248_);
v_val_4252_ = lean_ctor_get(v___x_4250_, 0);
lean_inc(v_val_4252_);
lean_dec_ref_known(v___x_4250_, 1);
v___x_4253_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4254_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4255_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4256_ = lean_string_intercalate(v___x_4255_, v_val_4252_);
v___x_4257_ = lean_string_append(v___x_4254_, v___x_4256_);
lean_dec_ref(v___x_4256_);
v___x_4258_ = lean_box(2);
v___x_4259_ = l_Lean_Syntax_mkNameLit(v___x_4257_, v___x_4258_);
v___x_4260_ = lean_unsigned_to_nat(1u);
v___x_4261_ = lean_mk_empty_array_with_capacity(v___x_4260_);
v___x_4262_ = lean_array_push(v___x_4261_, v___x_4259_);
v___x_4263_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4258_);
lean_ctor_set(v___x_4263_, 1, v___x_4253_);
lean_ctor_set(v___x_4263_, 2, v___x_4262_);
return v___x_4263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object* v_inst_4271_, lean_object* v_inst_4272_, lean_object* v_x_4273_){
_start:
{
lean_object* v_fst_4274_; lean_object* v_snd_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
v_fst_4274_ = lean_ctor_get(v_x_4273_, 0);
lean_inc(v_fst_4274_);
v_snd_4275_ = lean_ctor_get(v_x_4273_, 1);
lean_inc(v_snd_4275_);
lean_dec_ref(v_x_4273_);
v___x_4276_ = ((lean_object*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2));
v___x_4277_ = lean_apply_1(v_inst_4271_, v_fst_4274_);
v___x_4278_ = lean_apply_1(v_inst_4272_, v_snd_4275_);
v___x_4279_ = lean_unsigned_to_nat(2u);
v___x_4280_ = lean_mk_empty_array_with_capacity(v___x_4279_);
v___x_4281_ = lean_array_push(v___x_4280_, v___x_4277_);
v___x_4282_ = lean_array_push(v___x_4281_, v___x_4278_);
v___x_4283_ = l_Lean_Syntax_mkCApp(v___x_4276_, v___x_4282_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object* v_inst_4284_, lean_object* v_inst_4285_){
_start:
{
lean_object* v___f_4286_; 
v___f_4286_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4286_, 0, v_inst_4284_);
lean_closure_set(v___f_4286_, 1, v_inst_4285_);
return v___f_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object* v_00_u03b1_4287_, lean_object* v_00_u03b2_4288_, lean_object* v_inst_4289_, lean_object* v_inst_4290_){
_start:
{
lean_object* v___f_4291_; 
v___f_4291_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4291_, 0, v_inst_4289_);
lean_closure_set(v___f_4291_, 1, v_inst_4290_);
return v___f_4291_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3(void){
_start:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4297_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2));
v___x_4298_ = l_Lean_mkCIdent(v___x_4297_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object* v_inst_4303_, lean_object* v_x_4304_){
_start:
{
if (lean_obj_tag(v_x_4304_) == 0)
{
lean_object* v___x_4305_; 
lean_dec_ref(v_inst_4303_);
v___x_4305_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3);
return v___x_4305_;
}
else
{
lean_object* v_head_4306_; lean_object* v_tail_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
v_head_4306_ = lean_ctor_get(v_x_4304_, 0);
lean_inc(v_head_4306_);
v_tail_4307_ = lean_ctor_get(v_x_4304_, 1);
lean_inc(v_tail_4307_);
lean_dec_ref_known(v_x_4304_, 2);
v___x_4308_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5));
lean_inc_ref(v_inst_4303_);
v___x_4309_ = lean_apply_1(v_inst_4303_, v_head_4306_);
v___x_4310_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4303_, v_tail_4307_);
v___x_4311_ = lean_unsigned_to_nat(2u);
v___x_4312_ = lean_mk_empty_array_with_capacity(v___x_4311_);
v___x_4313_ = lean_array_push(v___x_4312_, v___x_4309_);
v___x_4314_ = lean_array_push(v___x_4313_, v___x_4310_);
v___x_4315_ = l_Lean_Syntax_mkCApp(v___x_4308_, v___x_4314_);
return v___x_4315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object* v_00_u03b1_4316_, lean_object* v_inst_4317_, lean_object* v_x_4318_){
_start:
{
lean_object* v___x_4319_; 
v___x_4319_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4317_, v_x_4318_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object* v_inst_4320_, lean_object* v_a_4321_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4320_, v_a_4321_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object* v_00_u03b1_4323_, lean_object* v_inst_4324_, lean_object* v_a_4325_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4324_, v_a_4325_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object* v_inst_4327_){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4328_, 0, lean_box(0));
lean_closure_set(v___x_4328_, 1, v_inst_4327_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object* v_00_u03b1_4329_, lean_object* v_inst_4330_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4331_, 0, lean_box(0));
lean_closure_set(v___x_4331_, 1, v_inst_4330_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object* v_inst_4334_, lean_object* v_xs_4335_, lean_object* v_i_4336_, lean_object* v_args_4337_){
_start:
{
lean_object* v___x_4338_; uint8_t v___x_4339_; 
v___x_4338_ = lean_array_get_size(v_xs_4335_);
v___x_4339_ = lean_nat_dec_lt(v_i_4336_, v___x_4338_);
if (v___x_4339_ == 0)
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
lean_dec(v_i_4336_);
lean_dec_ref(v_inst_4334_);
v___x_4340_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0));
v___x_4341_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1));
v___x_4342_ = l_Nat_reprFast(v___x_4338_);
v___x_4343_ = lean_string_append(v___x_4341_, v___x_4342_);
lean_dec_ref(v___x_4342_);
v___x_4344_ = l_Lean_Name_mkStr2(v___x_4340_, v___x_4343_);
v___x_4345_ = l_Lean_Syntax_mkCApp(v___x_4344_, v_args_4337_);
return v___x_4345_;
}
else
{
lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4346_ = lean_unsigned_to_nat(1u);
v___x_4347_ = lean_nat_add(v_i_4336_, v___x_4346_);
v___x_4348_ = lean_array_fget_borrowed(v_xs_4335_, v_i_4336_);
lean_dec(v_i_4336_);
lean_inc_ref(v_inst_4334_);
lean_inc(v___x_4348_);
v___x_4349_ = lean_apply_1(v_inst_4334_, v___x_4348_);
v___x_4350_ = lean_array_push(v_args_4337_, v___x_4349_);
v_i_4336_ = v___x_4347_;
v_args_4337_ = v___x_4350_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object* v_inst_4352_, lean_object* v_xs_4353_, lean_object* v_i_4354_, lean_object* v_args_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4352_, v_xs_4353_, v_i_4354_, v_args_4355_);
lean_dec_ref(v_xs_4353_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object* v_00_u03b1_4357_, lean_object* v_inst_4358_, lean_object* v_xs_4359_, lean_object* v_i_4360_, lean_object* v_args_4361_){
_start:
{
lean_object* v___x_4362_; 
v___x_4362_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4358_, v_xs_4359_, v_i_4360_, v_args_4361_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object* v_00_u03b1_4363_, lean_object* v_inst_4364_, lean_object* v_xs_4365_, lean_object* v_i_4366_, lean_object* v_args_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go(v_00_u03b1_4363_, v_inst_4364_, v_xs_4365_, v_i_4366_, v_args_4367_);
lean_dec_ref(v_xs_4365_);
return v_res_4368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object* v_inst_4373_, lean_object* v_xs_4374_){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; uint8_t v___x_4377_; 
v___x_4375_ = lean_array_get_size(v_xs_4374_);
v___x_4376_ = lean_unsigned_to_nat(8u);
v___x_4377_ = lean_nat_dec_le(v___x_4375_, v___x_4376_);
if (v___x_4377_ == 0)
{
lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4378_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1));
v___x_4379_ = lean_array_to_list(v_xs_4374_);
v___x_4380_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4373_, v___x_4379_);
v___x_4381_ = lean_unsigned_to_nat(1u);
v___x_4382_ = lean_mk_empty_array_with_capacity(v___x_4381_);
v___x_4383_ = lean_array_push(v___x_4382_, v___x_4380_);
v___x_4384_ = l_Lean_Syntax_mkCApp(v___x_4378_, v___x_4383_);
return v___x_4384_;
}
else
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4385_ = lean_unsigned_to_nat(0u);
v___x_4386_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4387_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4373_, v_xs_4374_, v___x_4385_, v___x_4386_);
lean_dec_ref(v_xs_4374_);
return v___x_4387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object* v_00_u03b1_4388_, lean_object* v_inst_4389_, lean_object* v_xs_4390_){
_start:
{
lean_object* v___x_4391_; 
v___x_4391_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4389_, v_xs_4390_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object* v_inst_4392_, lean_object* v_xs_4393_){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4392_, v_xs_4393_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object* v_00_u03b1_4395_, lean_object* v_inst_4396_, lean_object* v_xs_4397_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4396_, v_xs_4397_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object* v_inst_4399_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4400_, 0, lean_box(0));
lean_closure_set(v___x_4400_, 1, v_inst_4399_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object* v_00_u03b1_4401_, lean_object* v_inst_4402_){
_start:
{
lean_object* v___x_4403_; 
v___x_4403_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4403_, 0, lean_box(0));
lean_closure_set(v___x_4403_, 1, v_inst_4402_);
return v___x_4403_;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4409_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__2));
v___x_4410_ = l_Lean_mkIdent(v___x_4409_);
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object* v_inst_4415_, lean_object* v_x_4416_){
_start:
{
if (lean_obj_tag(v_x_4416_) == 0)
{
lean_object* v___x_4417_; 
lean_dec_ref(v_inst_4415_);
v___x_4417_ = lean_obj_once(&l_Lean_Option_hasQuote___redArg___lam__0___closed__3, &l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once, _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3);
return v___x_4417_;
}
else
{
lean_object* v_val_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v_val_4418_ = lean_ctor_get(v_x_4416_, 0);
lean_inc(v_val_4418_);
lean_dec_ref_known(v_x_4416_, 1);
v___x_4419_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__5));
v___x_4420_ = lean_apply_1(v_inst_4415_, v_val_4418_);
v___x_4421_ = lean_unsigned_to_nat(1u);
v___x_4422_ = lean_mk_empty_array_with_capacity(v___x_4421_);
v___x_4423_ = lean_array_push(v___x_4422_, v___x_4420_);
v___x_4424_ = l_Lean_Syntax_mkCApp(v___x_4419_, v___x_4423_);
return v___x_4424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object* v_inst_4425_){
_start:
{
lean_object* v___f_4426_; 
v___f_4426_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4426_, 0, v_inst_4425_);
return v___f_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object* v_00_u03b1_4427_, lean_object* v_inst_4428_){
_start:
{
lean_object* v___f_4429_; 
v___f_4429_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4429_, 0, v_inst_4428_);
return v___f_4429_;
}
}
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(lean_object* v_k_4430_){
_start:
{
lean_object* v___x_4431_; uint8_t v___x_4432_; uint8_t v___x_4433_; 
v___x_4431_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_4432_ = lean_name_eq(v_k_4430_, v___x_4431_);
v___x_4433_ = lean_bool_not(v___x_4432_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v_k_4434_){
_start:
{
uint8_t v_res_4435_; lean_object* v_r_4436_; 
v_res_4435_ = l_Lean_evalPrec___lam__0(v_k_4434_);
lean_dec(v_k_4434_);
v_r_4436_ = lean_box(v_res_4435_);
return v_r_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_){
_start:
{
lean_object* v_methods_4442_; lean_object* v_quotContext_4443_; lean_object* v_currMacroScope_4444_; lean_object* v_currRecDepth_4445_; lean_object* v_maxRecDepth_4446_; lean_object* v_ref_4447_; uint8_t v___x_4448_; 
v_methods_4442_ = lean_ctor_get(v_a_4440_, 0);
v_quotContext_4443_ = lean_ctor_get(v_a_4440_, 1);
v_currMacroScope_4444_ = lean_ctor_get(v_a_4440_, 2);
v_currRecDepth_4445_ = lean_ctor_get(v_a_4440_, 3);
v_maxRecDepth_4446_ = lean_ctor_get(v_a_4440_, 4);
v_ref_4447_ = lean_ctor_get(v_a_4440_, 5);
v___x_4448_ = lean_nat_dec_eq(v_currRecDepth_4445_, v_maxRecDepth_4446_);
if (v___x_4448_ == 0)
{
lean_object* v___f_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___f_4449_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4450_ = lean_unsigned_to_nat(1u);
v___x_4451_ = lean_nat_add(v_currRecDepth_4445_, v___x_4450_);
lean_inc(v_ref_4447_);
lean_inc(v_maxRecDepth_4446_);
lean_inc(v_currMacroScope_4444_);
lean_inc(v_quotContext_4443_);
lean_inc(v_methods_4442_);
v___x_4452_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4452_, 0, v_methods_4442_);
lean_ctor_set(v___x_4452_, 1, v_quotContext_4443_);
lean_ctor_set(v___x_4452_, 2, v_currMacroScope_4444_);
lean_ctor_set(v___x_4452_, 3, v___x_4451_);
lean_ctor_set(v___x_4452_, 4, v_maxRecDepth_4446_);
lean_ctor_set(v___x_4452_, 5, v_ref_4447_);
lean_inc_ref(v___x_4452_);
v___x_4453_ = l_Lean_expandMacros(v_stx_4439_, v___f_4449_, v___x_4452_, v_a_4441_);
if (lean_obj_tag(v___x_4453_) == 0)
{
lean_object* v_a_4454_; lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4467_; 
v_a_4454_ = lean_ctor_get(v___x_4453_, 0);
v_a_4455_ = lean_ctor_get(v___x_4453_, 1);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4453_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4457_ = v___x_4453_;
v_isShared_4458_ = v_isSharedCheck_4467_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_inc(v_a_4454_);
lean_dec(v___x_4453_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4467_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4459_; uint8_t v___x_4460_; 
v___x_4459_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4454_);
v___x_4460_ = l_Lean_Syntax_isOfKind(v_a_4454_, v___x_4459_);
if (v___x_4460_ == 0)
{
lean_object* v___x_4461_; lean_object* v___x_4462_; 
lean_del_object(v___x_4457_);
v___x_4461_ = ((lean_object*)(l_Lean_evalPrec___closed__1));
v___x_4462_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4454_, v___x_4461_, v___x_4452_, v_a_4455_);
lean_dec_ref_known(v___x_4452_, 6);
lean_dec(v_a_4454_);
return v___x_4462_;
}
else
{
lean_object* v___x_4463_; lean_object* v___x_4465_; 
lean_dec_ref_known(v___x_4452_, 6);
v___x_4463_ = l_Lean_TSyntax_getNat(v_a_4454_);
lean_dec(v_a_4454_);
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 0, v___x_4463_);
v___x_4465_ = v___x_4457_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4463_);
lean_ctor_set(v_reuseFailAlloc_4466_, 1, v_a_4455_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
else
{
lean_object* v_a_4468_; lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
lean_dec_ref_known(v___x_4452_, 6);
v_a_4468_ = lean_ctor_get(v___x_4453_, 0);
v_a_4469_ = lean_ctor_get(v___x_4453_, 1);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4453_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4453_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_inc(v_a_4468_);
lean_dec(v___x_4453_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4468_);
lean_ctor_set(v_reuseFailAlloc_4475_, 1, v_a_4469_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
}
else
{
lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
v___x_4477_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4478_, 0, v_stx_4439_);
lean_ctor_set(v___x_4478_, 1, v___x_4477_);
v___x_4479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4478_);
lean_ctor_set(v___x_4479_, 1, v_a_4441_);
return v___x_4479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object* v_stx_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Lean_evalPrec(v_stx_4480_, v_a_4481_, v_a_4482_);
lean_dec_ref(v_a_4481_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v_methods_4488_; lean_object* v_quotContext_4489_; lean_object* v_currMacroScope_4490_; lean_object* v_currRecDepth_4491_; lean_object* v_maxRecDepth_4492_; lean_object* v_ref_4493_; uint8_t v___x_4494_; 
v_methods_4488_ = lean_ctor_get(v_a_4486_, 0);
v_quotContext_4489_ = lean_ctor_get(v_a_4486_, 1);
v_currMacroScope_4490_ = lean_ctor_get(v_a_4486_, 2);
v_currRecDepth_4491_ = lean_ctor_get(v_a_4486_, 3);
v_maxRecDepth_4492_ = lean_ctor_get(v_a_4486_, 4);
v_ref_4493_ = lean_ctor_get(v_a_4486_, 5);
v___x_4494_ = lean_nat_dec_eq(v_currRecDepth_4491_, v_maxRecDepth_4492_);
if (v___x_4494_ == 0)
{
lean_object* v___f_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___f_4495_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4496_ = lean_unsigned_to_nat(1u);
v___x_4497_ = lean_nat_add(v_currRecDepth_4491_, v___x_4496_);
lean_inc(v_ref_4493_);
lean_inc(v_maxRecDepth_4492_);
lean_inc(v_currMacroScope_4490_);
lean_inc(v_quotContext_4489_);
lean_inc(v_methods_4488_);
v___x_4498_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4498_, 0, v_methods_4488_);
lean_ctor_set(v___x_4498_, 1, v_quotContext_4489_);
lean_ctor_set(v___x_4498_, 2, v_currMacroScope_4490_);
lean_ctor_set(v___x_4498_, 3, v___x_4497_);
lean_ctor_set(v___x_4498_, 4, v_maxRecDepth_4492_);
lean_ctor_set(v___x_4498_, 5, v_ref_4493_);
lean_inc_ref(v___x_4498_);
v___x_4499_ = l_Lean_expandMacros(v_stx_4485_, v___f_4495_, v___x_4498_, v_a_4487_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v_a_4500_; lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4513_; 
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
v_a_4501_ = lean_ctor_get(v___x_4499_, 1);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4503_ = v___x_4499_;
v_isShared_4504_ = v_isSharedCheck_4513_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_inc(v_a_4500_);
lean_dec(v___x_4499_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4513_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4505_; uint8_t v___x_4506_; 
v___x_4505_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4500_);
v___x_4506_ = l_Lean_Syntax_isOfKind(v_a_4500_, v___x_4505_);
if (v___x_4506_ == 0)
{
lean_object* v___x_4507_; lean_object* v___x_4508_; 
lean_del_object(v___x_4503_);
v___x_4507_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
v___x_4508_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4500_, v___x_4507_, v___x_4498_, v_a_4501_);
lean_dec_ref_known(v___x_4498_, 6);
lean_dec(v_a_4500_);
return v___x_4508_;
}
else
{
lean_object* v___x_4509_; lean_object* v___x_4511_; 
lean_dec_ref_known(v___x_4498_, 6);
v___x_4509_ = l_Lean_TSyntax_getNat(v_a_4500_);
lean_dec(v_a_4500_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 0, v___x_4509_);
v___x_4511_ = v___x_4503_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4509_);
lean_ctor_set(v_reuseFailAlloc_4512_, 1, v_a_4501_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
else
{
lean_object* v_a_4514_; lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
lean_dec_ref_known(v___x_4498_, 6);
v_a_4514_ = lean_ctor_get(v___x_4499_, 0);
v_a_4515_ = lean_ctor_get(v___x_4499_, 1);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4499_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_inc(v_a_4514_);
lean_dec(v___x_4499_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4514_);
lean_ctor_set(v_reuseFailAlloc_4521_, 1, v_a_4515_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
else
{
lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4523_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4524_, 0, v_stx_4485_);
lean_ctor_set(v___x_4524_, 1, v___x_4523_);
v___x_4525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4524_);
lean_ctor_set(v___x_4525_, 1, v_a_4487_);
return v___x_4525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object* v_stx_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l_Lean_evalPrio(v_stx_4526_, v_a_4527_, v_a_4528_);
lean_dec_ref(v_a_4527_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_){
_start:
{
if (lean_obj_tag(v_x_4530_) == 0)
{
lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4533_ = lean_unsigned_to_nat(1000u);
v___x_4534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4533_);
lean_ctor_set(v___x_4534_, 1, v_a_4532_);
return v___x_4534_;
}
else
{
lean_object* v_val_4535_; lean_object* v___x_4536_; 
v_val_4535_ = lean_ctor_get(v_x_4530_, 0);
lean_inc(v_val_4535_);
lean_dec_ref_known(v_x_4530_, 1);
v___x_4536_ = l_Lean_evalPrio(v_val_4535_, v_a_4531_, v_a_4532_);
return v___x_4536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object* v_x_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_Lean_evalOptPrio(v_x_4537_, v_a_4538_, v_a_4539_);
lean_dec_ref(v_a_4538_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4541_, lean_object* v_x1_4542_, lean_object* v_x2_4543_){
_start:
{
lean_object* v_fst_4544_; uint8_t v___x_4545_; 
v_fst_4544_ = lean_ctor_get(v_x1_4542_, 0);
v___x_4545_ = lean_unbox(v_fst_4544_);
if (v___x_4545_ == 0)
{
lean_object* v_snd_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4554_; 
lean_dec(v_x2_4543_);
v_snd_4546_ = lean_ctor_get(v_x1_4542_, 1);
v_isSharedCheck_4554_ = !lean_is_exclusive(v_x1_4542_);
if (v_isSharedCheck_4554_ == 0)
{
lean_object* v_unused_4555_; 
v_unused_4555_ = lean_ctor_get(v_x1_4542_, 0);
lean_dec(v_unused_4555_);
v___x_4548_ = v_x1_4542_;
v_isShared_4549_ = v_isSharedCheck_4554_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_snd_4546_);
lean_dec(v_x1_4542_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4554_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4550_; lean_object* v___x_4552_; 
v___x_4550_ = lean_box(v___x_4541_);
if (v_isShared_4549_ == 0)
{
lean_ctor_set(v___x_4548_, 0, v___x_4550_);
v___x_4552_ = v___x_4548_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4550_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_snd_4546_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
}
else
{
lean_object* v_snd_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4566_; 
v_snd_4556_ = lean_ctor_get(v_x1_4542_, 1);
v_isSharedCheck_4566_ = !lean_is_exclusive(v_x1_4542_);
if (v_isSharedCheck_4566_ == 0)
{
lean_object* v_unused_4567_; 
v_unused_4567_ = lean_ctor_get(v_x1_4542_, 0);
lean_dec(v_unused_4567_);
v___x_4558_ = v_x1_4542_;
v_isShared_4559_ = v_isSharedCheck_4566_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_snd_4556_);
lean_dec(v_x1_4542_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4566_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
uint8_t v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4564_; 
v___x_4560_ = 0;
v___x_4561_ = lean_array_push(v_snd_4556_, v_x2_4543_);
v___x_4562_ = lean_box(v___x_4560_);
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 1, v___x_4561_);
lean_ctor_set(v___x_4558_, 0, v___x_4562_);
v___x_4564_ = v___x_4558_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4562_);
lean_ctor_set(v_reuseFailAlloc_4565_, 1, v___x_4561_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4568_, lean_object* v_x1_4569_, lean_object* v_x2_4570_){
_start:
{
uint8_t v___x_96__boxed_4571_; lean_object* v_res_4572_; 
v___x_96__boxed_4571_ = lean_unbox(v___x_4568_);
v_res_4572_ = l_Array_getSepElems___redArg___lam__0(v___x_96__boxed_4571_, v_x1_4569_, v_x2_4570_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4594_){
_start:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; uint8_t v___x_4599_; 
v___x_4595_ = lean_unsigned_to_nat(0u);
v___x_4596_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4597_ = lean_array_get_size(v_as_4594_);
v___x_4598_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4599_ = lean_nat_dec_lt(v___x_4595_, v___x_4597_);
if (v___x_4599_ == 0)
{
lean_dec_ref(v_as_4594_);
return v___x_4596_;
}
else
{
lean_object* v___x_4600_; lean_object* v___f_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; uint8_t v___x_4604_; 
v___x_4600_ = lean_box(v___x_4599_);
v___f_4601_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4601_, 0, v___x_4600_);
v___x_4602_ = lean_box(v___x_4599_);
v___x_4603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
lean_ctor_set(v___x_4603_, 1, v___x_4596_);
v___x_4604_ = lean_nat_dec_le(v___x_4597_, v___x_4597_);
if (v___x_4604_ == 0)
{
if (v___x_4599_ == 0)
{
lean_dec_ref_known(v___x_4603_, 2);
lean_dec_ref(v___f_4601_);
lean_dec_ref(v_as_4594_);
return v___x_4596_;
}
else
{
size_t v___x_4605_; size_t v___x_4606_; lean_object* v___x_4607_; lean_object* v_snd_4608_; 
v___x_4605_ = ((size_t)0ULL);
v___x_4606_ = lean_usize_of_nat(v___x_4597_);
v___x_4607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4598_, v___f_4601_, v_as_4594_, v___x_4605_, v___x_4606_, v___x_4603_);
v_snd_4608_ = lean_ctor_get(v___x_4607_, 1);
lean_inc(v_snd_4608_);
lean_dec(v___x_4607_);
return v_snd_4608_;
}
}
else
{
size_t v___x_4609_; size_t v___x_4610_; lean_object* v___x_4611_; lean_object* v_snd_4612_; 
v___x_4609_ = ((size_t)0ULL);
v___x_4610_ = lean_usize_of_nat(v___x_4597_);
v___x_4611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4598_, v___f_4601_, v_as_4594_, v___x_4609_, v___x_4610_, v___x_4603_);
v_snd_4612_ = lean_ctor_get(v___x_4611_, 1);
lean_inc(v_snd_4612_);
lean_dec(v___x_4611_);
return v_snd_4612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4613_, lean_object* v_as_4614_){
_start:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; uint8_t v___x_4619_; 
v___x_4615_ = lean_unsigned_to_nat(0u);
v___x_4616_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4617_ = lean_array_get_size(v_as_4614_);
v___x_4618_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4619_ = lean_nat_dec_lt(v___x_4615_, v___x_4617_);
if (v___x_4619_ == 0)
{
lean_dec_ref(v_as_4614_);
return v___x_4616_;
}
else
{
lean_object* v___x_4620_; lean_object* v___f_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; uint8_t v___x_4624_; 
v___x_4620_ = lean_box(v___x_4619_);
v___f_4621_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4621_, 0, v___x_4620_);
v___x_4622_ = lean_box(v___x_4619_);
v___x_4623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4622_);
lean_ctor_set(v___x_4623_, 1, v___x_4616_);
v___x_4624_ = lean_nat_dec_le(v___x_4617_, v___x_4617_);
if (v___x_4624_ == 0)
{
if (v___x_4619_ == 0)
{
lean_dec_ref_known(v___x_4623_, 2);
lean_dec_ref(v___f_4621_);
lean_dec_ref(v_as_4614_);
return v___x_4616_;
}
else
{
size_t v___x_4625_; size_t v___x_4626_; lean_object* v___x_4627_; lean_object* v_snd_4628_; 
v___x_4625_ = ((size_t)0ULL);
v___x_4626_ = lean_usize_of_nat(v___x_4617_);
v___x_4627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4618_, v___f_4621_, v_as_4614_, v___x_4625_, v___x_4626_, v___x_4623_);
v_snd_4628_ = lean_ctor_get(v___x_4627_, 1);
lean_inc(v_snd_4628_);
lean_dec(v___x_4627_);
return v_snd_4628_;
}
}
else
{
size_t v___x_4629_; size_t v___x_4630_; lean_object* v___x_4631_; lean_object* v_snd_4632_; 
v___x_4629_ = ((size_t)0ULL);
v___x_4630_ = lean_usize_of_nat(v___x_4617_);
v___x_4631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4618_, v___f_4621_, v_as_4614_, v___x_4629_, v___x_4630_, v___x_4623_);
v_snd_4632_ = lean_ctor_get(v___x_4631_, 1);
lean_inc(v_snd_4632_);
lean_dec(v___x_4631_);
return v_snd_4632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4633_, lean_object* v_inst_4634_, lean_object* v_a_4635_, lean_object* v_p_4636_, lean_object* v_acc_4637_, lean_object* v_stx_4638_, uint8_t v_____do__lift_4639_){
_start:
{
if (v_____do__lift_4639_ == 0)
{
lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; 
lean_dec(v_stx_4638_);
v___x_4648_ = lean_unsigned_to_nat(2u);
v___x_4649_ = lean_nat_add(v_i_4633_, v___x_4648_);
v___x_4650_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4634_, v_a_4635_, v_p_4636_, v___x_4649_, v_acc_4637_);
return v___x_4650_;
}
else
{
lean_object* v___x_4651_; lean_object* v___x_4652_; uint8_t v___x_4653_; 
v___x_4651_ = lean_array_get_size(v_acc_4637_);
v___x_4652_ = lean_unsigned_to_nat(0u);
v___x_4653_ = lean_nat_dec_eq(v___x_4651_, v___x_4652_);
if (v___x_4653_ == 0)
{
uint8_t v___x_4654_; 
v___x_4654_ = lean_nat_dec_eq(v_i_4633_, v___x_4652_);
if (v___x_4654_ == 0)
{
goto v___jp_4640_;
}
else
{
if (v___x_4653_ == 0)
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4655_ = lean_unsigned_to_nat(2u);
v___x_4656_ = lean_nat_add(v_i_4633_, v___x_4655_);
v___x_4657_ = lean_array_push(v_acc_4637_, v_stx_4638_);
v___x_4658_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4634_, v_a_4635_, v_p_4636_, v___x_4656_, v___x_4657_);
return v___x_4658_;
}
else
{
goto v___jp_4640_;
}
}
}
else
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4659_ = lean_unsigned_to_nat(2u);
v___x_4660_ = lean_nat_add(v_i_4633_, v___x_4659_);
v___x_4661_ = lean_array_push(v_acc_4637_, v_stx_4638_);
v___x_4662_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4634_, v_a_4635_, v_p_4636_, v___x_4660_, v___x_4661_);
return v___x_4662_;
}
}
v___jp_4640_:
{
lean_object* v___x_4641_; lean_object* v_sepStx_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4641_ = lean_nat_pred(v_i_4633_);
v_sepStx_4642_ = lean_array_fget_borrowed(v_a_4635_, v___x_4641_);
lean_dec(v___x_4641_);
v___x_4643_ = lean_unsigned_to_nat(2u);
v___x_4644_ = lean_nat_add(v_i_4633_, v___x_4643_);
lean_inc(v_sepStx_4642_);
v___x_4645_ = lean_array_push(v_acc_4637_, v_sepStx_4642_);
v___x_4646_ = lean_array_push(v___x_4645_, v_stx_4638_);
v___x_4647_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4634_, v_a_4635_, v_p_4636_, v___x_4644_, v___x_4646_);
return v___x_4647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4663_, lean_object* v_inst_4664_, lean_object* v_a_4665_, lean_object* v_p_4666_, lean_object* v_acc_4667_, lean_object* v_stx_4668_, lean_object* v_____do__lift_4669_){
_start:
{
uint8_t v_____do__lift_284__boxed_4670_; lean_object* v_res_4671_; 
v_____do__lift_284__boxed_4670_ = lean_unbox(v_____do__lift_4669_);
v_res_4671_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4663_, v_inst_4664_, v_a_4665_, v_p_4666_, v_acc_4667_, v_stx_4668_, v_____do__lift_284__boxed_4670_);
lean_dec(v_i_4663_);
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4672_, lean_object* v_a_4673_, lean_object* v_p_4674_, lean_object* v_i_4675_, lean_object* v_acc_4676_){
_start:
{
lean_object* v___x_4677_; uint8_t v___x_4678_; 
v___x_4677_ = lean_array_get_size(v_a_4673_);
v___x_4678_ = lean_nat_dec_lt(v_i_4675_, v___x_4677_);
if (v___x_4678_ == 0)
{
lean_object* v_toApplicative_4679_; lean_object* v_toPure_4680_; lean_object* v___x_4681_; 
lean_dec(v_i_4675_);
lean_dec(v_p_4674_);
lean_dec_ref(v_a_4673_);
v_toApplicative_4679_ = lean_ctor_get(v_inst_4672_, 0);
lean_inc_ref(v_toApplicative_4679_);
lean_dec_ref(v_inst_4672_);
v_toPure_4680_ = lean_ctor_get(v_toApplicative_4679_, 1);
lean_inc(v_toPure_4680_);
lean_dec_ref(v_toApplicative_4679_);
v___x_4681_ = lean_apply_2(v_toPure_4680_, lean_box(0), v_acc_4676_);
return v___x_4681_;
}
else
{
lean_object* v_toBind_4682_; lean_object* v_stx_4683_; lean_object* v___f_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
v_toBind_4682_ = lean_ctor_get(v_inst_4672_, 1);
lean_inc(v_toBind_4682_);
v_stx_4683_ = lean_array_fget(v_a_4673_, v_i_4675_);
lean_inc(v_stx_4683_);
lean_inc(v_p_4674_);
v___f_4684_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4684_, 0, v_i_4675_);
lean_closure_set(v___f_4684_, 1, v_inst_4672_);
lean_closure_set(v___f_4684_, 2, v_a_4673_);
lean_closure_set(v___f_4684_, 3, v_p_4674_);
lean_closure_set(v___f_4684_, 4, v_acc_4676_);
lean_closure_set(v___f_4684_, 5, v_stx_4683_);
v___x_4685_ = lean_apply_1(v_p_4674_, v_stx_4683_);
v___x_4686_ = lean_apply_4(v_toBind_4682_, lean_box(0), lean_box(0), v___x_4685_, v___f_4684_);
return v___x_4686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4687_, lean_object* v_inst_4688_, lean_object* v_a_4689_, lean_object* v_p_4690_, lean_object* v_i_4691_, lean_object* v_acc_4692_){
_start:
{
lean_object* v___x_4693_; 
v___x_4693_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4688_, v_a_4689_, v_p_4690_, v_i_4691_, v_acc_4692_);
return v___x_4693_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4694_, lean_object* v_a_4695_, lean_object* v_p_4696_){
_start:
{
lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4697_ = lean_unsigned_to_nat(0u);
v___x_4698_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4699_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4694_, v_a_4695_, v_p_4696_, v___x_4697_, v___x_4698_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4700_, lean_object* v_inst_4701_, lean_object* v_a_4702_, lean_object* v_p_4703_){
_start:
{
lean_object* v___x_4704_; 
v___x_4704_ = l_Array_filterSepElemsM___redArg(v_inst_4701_, v_a_4702_, v_p_4703_);
return v___x_4704_;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4705_, lean_object* v_x_4706_){
_start:
{
lean_object* v___x_4707_; uint8_t v___x_4708_; 
v___x_4707_ = lean_apply_1(v_p_4705_, v_x_4706_);
v___x_4708_ = lean_unbox(v___x_4707_);
return v___x_4708_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4709_, lean_object* v_x_4710_){
_start:
{
uint8_t v_res_4711_; lean_object* v_r_4712_; 
v_res_4711_ = l_Array_filterSepElems___lam__0(v_p_4709_, v_x_4710_);
v_r_4712_ = lean_box(v_res_4711_);
return v_r_4712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4713_, lean_object* v_p_4714_, lean_object* v_i_4715_, lean_object* v_acc_4716_){
_start:
{
lean_object* v___x_4717_; uint8_t v___x_4718_; 
v___x_4717_ = lean_array_get_size(v_a_4713_);
v___x_4718_ = lean_nat_dec_lt(v_i_4715_, v___x_4717_);
if (v___x_4718_ == 0)
{
lean_dec(v_i_4715_);
lean_dec_ref(v_p_4714_);
return v_acc_4716_;
}
else
{
lean_object* v_stx_4719_; lean_object* v___x_4728_; uint8_t v___x_4729_; 
v_stx_4719_ = lean_array_fget_borrowed(v_a_4713_, v_i_4715_);
lean_inc_ref(v_p_4714_);
lean_inc(v_stx_4719_);
v___x_4728_ = lean_apply_1(v_p_4714_, v_stx_4719_);
v___x_4729_ = lean_unbox(v___x_4728_);
if (v___x_4729_ == 0)
{
lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4730_ = lean_unsigned_to_nat(2u);
v___x_4731_ = lean_nat_add(v_i_4715_, v___x_4730_);
lean_dec(v_i_4715_);
v_i_4715_ = v___x_4731_;
goto _start;
}
else
{
lean_object* v___x_4733_; lean_object* v___x_4734_; uint8_t v___x_4735_; 
v___x_4733_ = lean_array_get_size(v_acc_4716_);
v___x_4734_ = lean_unsigned_to_nat(0u);
v___x_4735_ = lean_nat_dec_eq(v___x_4733_, v___x_4734_);
if (v___x_4735_ == 0)
{
uint8_t v___x_4736_; 
v___x_4736_ = lean_nat_dec_eq(v_i_4715_, v___x_4734_);
if (v___x_4736_ == 0)
{
goto v___jp_4720_;
}
else
{
if (v___x_4735_ == 0)
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4737_ = lean_unsigned_to_nat(2u);
v___x_4738_ = lean_nat_add(v_i_4715_, v___x_4737_);
lean_dec(v_i_4715_);
lean_inc(v_stx_4719_);
v___x_4739_ = lean_array_push(v_acc_4716_, v_stx_4719_);
v_i_4715_ = v___x_4738_;
v_acc_4716_ = v___x_4739_;
goto _start;
}
else
{
goto v___jp_4720_;
}
}
}
else
{
lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v___x_4741_ = lean_unsigned_to_nat(2u);
v___x_4742_ = lean_nat_add(v_i_4715_, v___x_4741_);
lean_dec(v_i_4715_);
lean_inc(v_stx_4719_);
v___x_4743_ = lean_array_push(v_acc_4716_, v_stx_4719_);
v_i_4715_ = v___x_4742_;
v_acc_4716_ = v___x_4743_;
goto _start;
}
}
v___jp_4720_:
{
lean_object* v___x_4721_; lean_object* v_sepStx_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; 
v___x_4721_ = lean_nat_pred(v_i_4715_);
v_sepStx_4722_ = lean_array_fget_borrowed(v_a_4713_, v___x_4721_);
lean_dec(v___x_4721_);
v___x_4723_ = lean_unsigned_to_nat(2u);
v___x_4724_ = lean_nat_add(v_i_4715_, v___x_4723_);
lean_dec(v_i_4715_);
lean_inc(v_sepStx_4722_);
v___x_4725_ = lean_array_push(v_acc_4716_, v_sepStx_4722_);
lean_inc(v_stx_4719_);
v___x_4726_ = lean_array_push(v___x_4725_, v_stx_4719_);
v_i_4715_ = v___x_4724_;
v_acc_4716_ = v___x_4726_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4745_, lean_object* v_p_4746_, lean_object* v_i_4747_, lean_object* v_acc_4748_){
_start:
{
lean_object* v_res_4749_; 
v_res_4749_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4745_, v_p_4746_, v_i_4747_, v_acc_4748_);
lean_dec_ref(v_a_4745_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4750_, lean_object* v_p_4751_){
_start:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4752_ = lean_unsigned_to_nat(0u);
v___x_4753_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4754_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4750_, v_p_4751_, v___x_4752_, v___x_4753_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4755_, lean_object* v_p_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4755_, v_p_4756_);
lean_dec_ref(v_a_4755_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4758_, lean_object* v_p_4759_){
_start:
{
lean_object* v___f_4760_; lean_object* v___x_4761_; 
v___f_4760_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4760_, 0, v_p_4759_);
v___x_4761_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4758_, v___f_4760_);
return v___x_4761_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4762_, lean_object* v_p_4763_){
_start:
{
lean_object* v_res_4764_; 
v_res_4764_ = l_Array_filterSepElems(v_a_4762_, v_p_4763_);
lean_dec_ref(v_a_4762_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4765_, lean_object* v_acc_4766_, lean_object* v_inst_4767_, lean_object* v_a_4768_, lean_object* v_f_4769_, lean_object* v_stx_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4765_, v_acc_4766_, v_inst_4767_, v_a_4768_, v_f_4769_, v_stx_4770_);
lean_dec(v_i_4765_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4772_, lean_object* v_a_4773_, lean_object* v_f_4774_, lean_object* v_i_4775_, lean_object* v_acc_4776_){
_start:
{
lean_object* v___x_4777_; uint8_t v___x_4778_; 
v___x_4777_ = lean_array_get_size(v_a_4773_);
v___x_4778_ = lean_nat_dec_lt(v_i_4775_, v___x_4777_);
if (v___x_4778_ == 0)
{
lean_object* v_toApplicative_4779_; lean_object* v_toPure_4780_; lean_object* v___x_4781_; 
lean_dec(v_i_4775_);
lean_dec(v_f_4774_);
lean_dec_ref(v_a_4773_);
v_toApplicative_4779_ = lean_ctor_get(v_inst_4772_, 0);
lean_inc_ref(v_toApplicative_4779_);
lean_dec_ref(v_inst_4772_);
v_toPure_4780_ = lean_ctor_get(v_toApplicative_4779_, 1);
lean_inc(v_toPure_4780_);
lean_dec_ref(v_toApplicative_4779_);
v___x_4781_ = lean_apply_2(v_toPure_4780_, lean_box(0), v_acc_4776_);
return v___x_4781_;
}
else
{
lean_object* v_stx_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; uint8_t v___x_4786_; 
v_stx_4782_ = lean_array_fget_borrowed(v_a_4773_, v_i_4775_);
v___x_4783_ = lean_unsigned_to_nat(2u);
v___x_4784_ = lean_nat_mod(v_i_4775_, v___x_4783_);
v___x_4785_ = lean_unsigned_to_nat(0u);
v___x_4786_ = lean_nat_dec_eq(v___x_4784_, v___x_4785_);
lean_dec(v___x_4784_);
if (v___x_4786_ == 0)
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4787_ = lean_unsigned_to_nat(1u);
v___x_4788_ = lean_nat_add(v_i_4775_, v___x_4787_);
lean_dec(v_i_4775_);
lean_inc(v_stx_4782_);
v___x_4789_ = lean_array_push(v_acc_4776_, v_stx_4782_);
v_i_4775_ = v___x_4788_;
v_acc_4776_ = v___x_4789_;
goto _start;
}
else
{
lean_object* v_toBind_4791_; lean_object* v___f_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
lean_inc(v_stx_4782_);
v_toBind_4791_ = lean_ctor_get(v_inst_4772_, 1);
lean_inc(v_toBind_4791_);
lean_inc(v_f_4774_);
v___f_4792_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4792_, 0, v_i_4775_);
lean_closure_set(v___f_4792_, 1, v_acc_4776_);
lean_closure_set(v___f_4792_, 2, v_inst_4772_);
lean_closure_set(v___f_4792_, 3, v_a_4773_);
lean_closure_set(v___f_4792_, 4, v_f_4774_);
v___x_4793_ = lean_apply_1(v_f_4774_, v_stx_4782_);
v___x_4794_ = lean_apply_4(v_toBind_4791_, lean_box(0), lean_box(0), v___x_4793_, v___f_4792_);
return v___x_4794_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4795_, lean_object* v_acc_4796_, lean_object* v_inst_4797_, lean_object* v_a_4798_, lean_object* v_f_4799_, lean_object* v_stx_4800_){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4801_ = lean_unsigned_to_nat(1u);
v___x_4802_ = lean_nat_add(v_i_4795_, v___x_4801_);
v___x_4803_ = lean_array_push(v_acc_4796_, v_stx_4800_);
v___x_4804_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4797_, v_a_4798_, v_f_4799_, v___x_4802_, v___x_4803_);
return v___x_4804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4805_, lean_object* v_inst_4806_, lean_object* v_a_4807_, lean_object* v_f_4808_, lean_object* v_i_4809_, lean_object* v_acc_4810_){
_start:
{
lean_object* v___x_4811_; 
v___x_4811_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4806_, v_a_4807_, v_f_4808_, v_i_4809_, v_acc_4810_);
return v___x_4811_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4812_, lean_object* v_a_4813_, lean_object* v_f_4814_){
_start:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4815_ = lean_unsigned_to_nat(0u);
v___x_4816_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4817_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4812_, v_a_4813_, v_f_4814_, v___x_4815_, v___x_4816_);
return v___x_4817_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4818_, lean_object* v_inst_4819_, lean_object* v_a_4820_, lean_object* v_f_4821_){
_start:
{
lean_object* v___x_4822_; 
v___x_4822_ = l_Array_mapSepElemsM___redArg(v_inst_4819_, v_a_4820_, v_f_4821_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4823_, lean_object* v_x_4824_){
_start:
{
lean_object* v___x_4825_; 
v___x_4825_ = lean_apply_1(v_f_4823_, v_x_4824_);
return v___x_4825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4826_, lean_object* v_f_4827_, lean_object* v_i_4828_, lean_object* v_acc_4829_){
_start:
{
lean_object* v___x_4830_; uint8_t v___x_4831_; 
v___x_4830_ = lean_array_get_size(v_a_4826_);
v___x_4831_ = lean_nat_dec_lt(v_i_4828_, v___x_4830_);
if (v___x_4831_ == 0)
{
lean_dec(v_i_4828_);
lean_dec_ref(v_f_4827_);
return v_acc_4829_;
}
else
{
lean_object* v_stx_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; uint8_t v___x_4836_; 
v_stx_4832_ = lean_array_fget_borrowed(v_a_4826_, v_i_4828_);
v___x_4833_ = lean_unsigned_to_nat(2u);
v___x_4834_ = lean_nat_mod(v_i_4828_, v___x_4833_);
v___x_4835_ = lean_unsigned_to_nat(0u);
v___x_4836_ = lean_nat_dec_eq(v___x_4834_, v___x_4835_);
lean_dec(v___x_4834_);
if (v___x_4836_ == 0)
{
lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4837_ = lean_unsigned_to_nat(1u);
v___x_4838_ = lean_nat_add(v_i_4828_, v___x_4837_);
lean_dec(v_i_4828_);
lean_inc(v_stx_4832_);
v___x_4839_ = lean_array_push(v_acc_4829_, v_stx_4832_);
v_i_4828_ = v___x_4838_;
v_acc_4829_ = v___x_4839_;
goto _start;
}
else
{
lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; 
lean_inc_ref(v_f_4827_);
lean_inc(v_stx_4832_);
v___x_4841_ = lean_apply_1(v_f_4827_, v_stx_4832_);
v___x_4842_ = lean_unsigned_to_nat(1u);
v___x_4843_ = lean_nat_add(v_i_4828_, v___x_4842_);
lean_dec(v_i_4828_);
v___x_4844_ = lean_array_push(v_acc_4829_, v___x_4841_);
v_i_4828_ = v___x_4843_;
v_acc_4829_ = v___x_4844_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4846_, lean_object* v_f_4847_, lean_object* v_i_4848_, lean_object* v_acc_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4846_, v_f_4847_, v_i_4848_, v_acc_4849_);
lean_dec_ref(v_a_4846_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4851_, lean_object* v_f_4852_){
_start:
{
lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4853_ = lean_unsigned_to_nat(0u);
v___x_4854_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4855_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4851_, v_f_4852_, v___x_4853_, v___x_4854_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4856_, lean_object* v_f_4857_){
_start:
{
lean_object* v_res_4858_; 
v_res_4858_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4856_, v_f_4857_);
lean_dec_ref(v_a_4856_);
return v_res_4858_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4859_, lean_object* v_f_4860_){
_start:
{
lean_object* v___f_4861_; lean_object* v___x_4862_; 
v___f_4861_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4861_, 0, v_f_4860_);
v___x_4862_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4859_, v___f_4861_);
return v___x_4862_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4863_, lean_object* v_f_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l_Array_mapSepElems(v_a_4863_, v_f_4864_);
lean_dec_ref(v_a_4863_);
return v_res_4865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4866_, size_t v_i_4867_, size_t v_stop_4868_, lean_object* v_b_4869_){
_start:
{
lean_object* v___y_4871_; uint8_t v___x_4875_; 
v___x_4875_ = lean_usize_dec_eq(v_i_4867_, v_stop_4868_);
if (v___x_4875_ == 0)
{
lean_object* v_fst_4876_; uint8_t v___x_4877_; 
v_fst_4876_ = lean_ctor_get(v_b_4869_, 0);
v___x_4877_ = lean_unbox(v_fst_4876_);
if (v___x_4877_ == 0)
{
lean_object* v_snd_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4887_; 
v_snd_4878_ = lean_ctor_get(v_b_4869_, 1);
v_isSharedCheck_4887_ = !lean_is_exclusive(v_b_4869_);
if (v_isSharedCheck_4887_ == 0)
{
lean_object* v_unused_4888_; 
v_unused_4888_ = lean_ctor_get(v_b_4869_, 0);
lean_dec(v_unused_4888_);
v___x_4880_ = v_b_4869_;
v_isShared_4881_ = v_isSharedCheck_4887_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_snd_4878_);
lean_dec(v_b_4869_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4887_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
uint8_t v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4885_; 
v___x_4882_ = 1;
v___x_4883_ = lean_box(v___x_4882_);
if (v_isShared_4881_ == 0)
{
lean_ctor_set(v___x_4880_, 0, v___x_4883_);
v___x_4885_ = v___x_4880_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4883_);
lean_ctor_set(v_reuseFailAlloc_4886_, 1, v_snd_4878_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
v___y_4871_ = v___x_4885_;
goto v___jp_4870_;
}
}
}
else
{
lean_object* v_snd_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4899_; 
v_snd_4889_ = lean_ctor_get(v_b_4869_, 1);
v_isSharedCheck_4899_ = !lean_is_exclusive(v_b_4869_);
if (v_isSharedCheck_4899_ == 0)
{
lean_object* v_unused_4900_; 
v_unused_4900_ = lean_ctor_get(v_b_4869_, 0);
lean_dec(v_unused_4900_);
v___x_4891_ = v_b_4869_;
v_isShared_4892_ = v_isSharedCheck_4899_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_snd_4889_);
lean_dec(v_b_4869_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4899_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4897_; 
v___x_4893_ = lean_array_uget_borrowed(v_as_4866_, v_i_4867_);
lean_inc(v___x_4893_);
v___x_4894_ = lean_array_push(v_snd_4889_, v___x_4893_);
v___x_4895_ = lean_box(v___x_4875_);
if (v_isShared_4892_ == 0)
{
lean_ctor_set(v___x_4891_, 1, v___x_4894_);
lean_ctor_set(v___x_4891_, 0, v___x_4895_);
v___x_4897_ = v___x_4891_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v___x_4895_);
lean_ctor_set(v_reuseFailAlloc_4898_, 1, v___x_4894_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
v___y_4871_ = v___x_4897_;
goto v___jp_4870_;
}
}
}
}
else
{
return v_b_4869_;
}
v___jp_4870_:
{
size_t v___x_4872_; size_t v___x_4873_; 
v___x_4872_ = ((size_t)1ULL);
v___x_4873_ = lean_usize_add(v_i_4867_, v___x_4872_);
v_i_4867_ = v___x_4873_;
v_b_4869_ = v___y_4871_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4901_, lean_object* v_i_4902_, lean_object* v_stop_4903_, lean_object* v_b_4904_){
_start:
{
size_t v_i_boxed_4905_; size_t v_stop_boxed_4906_; lean_object* v_res_4907_; 
v_i_boxed_4905_ = lean_unbox_usize(v_i_4902_);
lean_dec(v_i_4902_);
v_stop_boxed_4906_ = lean_unbox_usize(v_stop_4903_);
lean_dec(v_stop_4903_);
v_res_4907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4901_, v_i_boxed_4905_, v_stop_boxed_4906_, v_b_4904_);
lean_dec_ref(v_as_4901_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4908_){
_start:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; uint8_t v___x_4912_; 
v___x_4909_ = lean_unsigned_to_nat(0u);
v___x_4910_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4911_ = lean_array_get_size(v_sa_4908_);
v___x_4912_ = lean_nat_dec_lt(v___x_4909_, v___x_4911_);
if (v___x_4912_ == 0)
{
return v___x_4910_;
}
else
{
lean_object* v___x_4913_; lean_object* v___x_4914_; uint8_t v___x_4915_; 
v___x_4913_ = lean_box(v___x_4912_);
v___x_4914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4914_, 0, v___x_4913_);
lean_ctor_set(v___x_4914_, 1, v___x_4910_);
v___x_4915_ = lean_nat_dec_le(v___x_4911_, v___x_4911_);
if (v___x_4915_ == 0)
{
if (v___x_4912_ == 0)
{
lean_dec_ref_known(v___x_4914_, 2);
return v___x_4910_;
}
else
{
size_t v___x_4916_; size_t v___x_4917_; lean_object* v___x_4918_; lean_object* v_snd_4919_; 
v___x_4916_ = ((size_t)0ULL);
v___x_4917_ = lean_usize_of_nat(v___x_4911_);
v___x_4918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4908_, v___x_4916_, v___x_4917_, v___x_4914_);
v_snd_4919_ = lean_ctor_get(v___x_4918_, 1);
lean_inc(v_snd_4919_);
lean_dec_ref(v___x_4918_);
return v_snd_4919_;
}
}
else
{
size_t v___x_4920_; size_t v___x_4921_; lean_object* v___x_4922_; lean_object* v_snd_4923_; 
v___x_4920_ = ((size_t)0ULL);
v___x_4921_ = lean_usize_of_nat(v___x_4911_);
v___x_4922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4908_, v___x_4920_, v___x_4921_, v___x_4914_);
v_snd_4923_ = lean_ctor_get(v___x_4922_, 1);
lean_inc(v_snd_4923_);
lean_dec_ref(v___x_4922_);
return v_snd_4923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4924_){
_start:
{
lean_object* v_res_4925_; 
v_res_4925_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4924_);
lean_dec_ref(v_sa_4924_);
return v_res_4925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4926_, lean_object* v_sa_4927_){
_start:
{
lean_object* v___x_4928_; 
v___x_4928_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4927_);
return v___x_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4929_, lean_object* v_sa_4930_){
_start:
{
lean_object* v_res_4931_; 
v_res_4931_ = l_Lean_Syntax_SepArray_getElems(v_sep_4929_, v_sa_4930_);
lean_dec_ref(v_sa_4930_);
lean_dec_ref(v_sep_4929_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4932_){
_start:
{
lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; uint8_t v___x_4936_; 
v___x_4933_ = lean_unsigned_to_nat(0u);
v___x_4934_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4935_ = lean_array_get_size(v_sa_4932_);
v___x_4936_ = lean_nat_dec_lt(v___x_4933_, v___x_4935_);
if (v___x_4936_ == 0)
{
return v___x_4934_;
}
else
{
lean_object* v___x_4937_; lean_object* v___x_4938_; uint8_t v___x_4939_; 
v___x_4937_ = lean_box(v___x_4936_);
v___x_4938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4937_);
lean_ctor_set(v___x_4938_, 1, v___x_4934_);
v___x_4939_ = lean_nat_dec_le(v___x_4935_, v___x_4935_);
if (v___x_4939_ == 0)
{
if (v___x_4936_ == 0)
{
lean_dec_ref_known(v___x_4938_, 2);
return v___x_4934_;
}
else
{
size_t v___x_4940_; size_t v___x_4941_; lean_object* v___x_4942_; lean_object* v_snd_4943_; 
v___x_4940_ = ((size_t)0ULL);
v___x_4941_ = lean_usize_of_nat(v___x_4935_);
v___x_4942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4932_, v___x_4940_, v___x_4941_, v___x_4938_);
v_snd_4943_ = lean_ctor_get(v___x_4942_, 1);
lean_inc(v_snd_4943_);
lean_dec_ref(v___x_4942_);
return v_snd_4943_;
}
}
else
{
size_t v___x_4944_; size_t v___x_4945_; lean_object* v___x_4946_; lean_object* v_snd_4947_; 
v___x_4944_ = ((size_t)0ULL);
v___x_4945_ = lean_usize_of_nat(v___x_4935_);
v___x_4946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4932_, v___x_4944_, v___x_4945_, v___x_4938_);
v_snd_4947_ = lean_ctor_get(v___x_4946_, 1);
lean_inc(v_snd_4947_);
lean_dec_ref(v___x_4946_);
return v_snd_4947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4948_){
_start:
{
lean_object* v_res_4949_; 
v_res_4949_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4948_);
lean_dec_ref(v_sa_4948_);
return v_res_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4950_, lean_object* v_sep_4951_, lean_object* v_sa_4952_){
_start:
{
lean_object* v___x_4953_; 
v___x_4953_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4952_);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4954_, lean_object* v_sep_4955_, lean_object* v_sa_4956_){
_start:
{
lean_object* v_res_4957_; 
v_res_4957_ = l_Lean_Syntax_TSepArray_getElems(v_k_4954_, v_sep_4955_, v_sa_4956_);
lean_dec_ref(v_sa_4956_);
lean_dec_ref(v_sep_4955_);
lean_dec(v_k_4954_);
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4958_, lean_object* v_sa_4959_, lean_object* v_e_4960_){
_start:
{
lean_object* v___x_4961_; lean_object* v___x_4962_; uint8_t v___x_4963_; 
v___x_4961_ = lean_array_get_size(v_sa_4959_);
v___x_4962_ = lean_unsigned_to_nat(0u);
v___x_4963_ = lean_nat_dec_eq(v___x_4961_, v___x_4962_);
if (v___x_4963_ == 0)
{
lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4964_ = l_Lean_mkAtom(v_sep_4958_);
v___x_4965_ = lean_array_push(v_sa_4959_, v___x_4964_);
v___x_4966_ = lean_array_push(v___x_4965_, v_e_4960_);
return v___x_4966_;
}
else
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
lean_dec_ref(v_sa_4959_);
lean_dec_ref(v_sep_4958_);
v___x_4967_ = lean_unsigned_to_nat(1u);
v___x_4968_ = lean_mk_empty_array_with_capacity(v___x_4967_);
v___x_4969_ = lean_array_push(v___x_4968_, v_e_4960_);
return v___x_4969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_4970_, lean_object* v_sep_4971_, lean_object* v_sa_4972_, lean_object* v_e_4973_){
_start:
{
lean_object* v___x_4974_; 
v___x_4974_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_4971_, v_sa_4972_, v_e_4973_);
return v___x_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_4975_, lean_object* v_sep_4976_, lean_object* v_sa_4977_, lean_object* v_e_4978_){
_start:
{
lean_object* v_res_4979_; 
v_res_4979_ = l_Lean_Syntax_TSepArray_push(v_k_4975_, v_sep_4976_, v_sa_4977_, v_e_4978_);
lean_dec(v_k_4975_);
return v_res_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_4980_){
_start:
{
lean_object* v___x_4981_; 
v___x_4981_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_4982_);
lean_dec_ref(v_sep_4982_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_4984_, lean_object* v_k_4985_){
_start:
{
lean_object* v___x_4986_; 
v___x_4986_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_4987_, lean_object* v_k_4988_){
_start:
{
lean_object* v_res_4989_; 
v_res_4989_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_4987_, v_k_4988_);
lean_dec_ref(v_k_4988_);
lean_dec(v_sep_4987_);
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutSepArrayArray(lean_object* v_sep_4990_){
_start:
{
lean_object* v___x_4991_; 
v___x_4991_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_getElems___boxed), 2, 1);
lean_closure_set(v___x_4991_, 0, v_sep_4990_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_4992_, lean_object* v_sep_4993_){
_start:
{
lean_object* v___x_4994_; 
v___x_4994_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_4994_, 0, v_k_4992_);
lean_closure_set(v___x_4994_, 1, v_sep_4993_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_4995_, lean_object* v_x_4996_){
_start:
{
lean_object* v___x_4997_; 
v___x_4997_ = lean_apply_1(v_inst_4995_, v_x_4996_);
return v___x_4997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_4998_, lean_object* v_a_4999_){
_start:
{
lean_object* v___x_5000_; size_t v_sz_5001_; size_t v___x_5002_; lean_object* v___x_5003_; 
v___x_5000_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_5001_ = lean_array_size(v_a_4999_);
v___x_5002_ = ((size_t)0ULL);
v___x_5003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5000_, v___f_4998_, v_sz_5001_, v___x_5002_, v_a_4999_);
return v___x_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_5004_){
_start:
{
lean_object* v___f_5005_; lean_object* v___f_5006_; 
v___f_5005_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5005_, 0, v_inst_5004_);
v___f_5006_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5006_, 0, v___f_5005_);
return v___f_5006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_5007_, lean_object* v_k_x27_5008_, lean_object* v_inst_5009_){
_start:
{
lean_object* v___x_5010_; 
v___x_5010_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_5009_);
return v___x_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_5011_, lean_object* v_k_x27_5012_, lean_object* v_inst_5013_){
_start:
{
lean_object* v_res_5014_; 
v_res_5014_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_5011_, v_k_x27_5012_, v_inst_5013_);
lean_dec(v_k_x27_5012_);
lean_dec(v_k_5011_);
return v_res_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(lean_object* v_a_5015_){
_start:
{
lean_inc_ref(v_a_5015_);
return v_a_5015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0___boxed(lean_object* v_a_5016_){
_start:
{
lean_object* v_res_5017_; 
v_res_5017_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(v_a_5016_);
lean_dec_ref(v_a_5016_);
return v_res_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_5019_){
_start:
{
lean_object* v___f_5020_; 
v___f_5020_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0));
return v___f_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* v_k_5021_){
_start:
{
lean_object* v_res_5022_; 
v_res_5022_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(v_k_5021_);
lean_dec(v_k_5021_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_5030_){
_start:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5031_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2));
v___x_5032_ = lean_box(2);
v___x_5033_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
v___x_5034_ = lean_unsigned_to_nat(2u);
v___x_5035_ = lean_mk_empty_array_with_capacity(v___x_5034_);
v___x_5036_ = lean_array_push(v___x_5035_, v_id_5030_);
v___x_5037_ = lean_array_push(v___x_5036_, v___x_5033_);
v___x_5038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5032_);
lean_ctor_set(v___x_5038_, 1, v___x_5031_);
lean_ctor_set(v___x_5038_, 2, v___x_5037_);
return v___x_5038_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_5042_; lean_object* v___x_5043_; 
v___x_5042_ = 123;
v___x_5043_ = lean_box_uint32(v___x_5042_);
return v___x_5043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* v_s_5044_, lean_object* v_i_5045_){
_start:
{
lean_object* v___x_5046_; 
v___x_5046_ = l_Lean_Syntax_decodeQuotedChar(v_s_5044_, v_i_5045_);
if (lean_obj_tag(v___x_5046_) == 0)
{
uint32_t v_c_5047_; uint32_t v___x_5048_; uint8_t v___x_5049_; 
v_c_5047_ = lean_string_utf8_get(v_s_5044_, v_i_5045_);
v___x_5048_ = 123;
v___x_5049_ = lean_uint32_dec_eq(v_c_5047_, v___x_5048_);
if (v___x_5049_ == 0)
{
return v___x_5046_;
}
else
{
lean_object* v_i_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v_i_5050_ = lean_string_utf8_next(v_s_5044_, v_i_5045_);
v___x_5051_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
v___x_5052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5051_);
lean_ctor_set(v___x_5052_, 1, v_i_5050_);
v___x_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5053_, 0, v___x_5052_);
return v___x_5053_;
}
}
else
{
return v___x_5046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* v_s_5054_, lean_object* v_i_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5054_, v_i_5055_);
lean_dec(v_i_5055_);
lean_dec_ref(v_s_5054_);
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* v_s_5057_, lean_object* v_i_5058_, lean_object* v_acc_5059_){
_start:
{
uint32_t v_c_5060_; lean_object* v_i_5061_; uint8_t v___y_5063_; uint32_t v___x_5082_; uint8_t v___x_5083_; 
v_c_5060_ = lean_string_utf8_get(v_s_5057_, v_i_5058_);
v_i_5061_ = lean_string_utf8_next(v_s_5057_, v_i_5058_);
lean_dec(v_i_5058_);
v___x_5082_ = 34;
v___x_5083_ = lean_uint32_dec_eq(v_c_5060_, v___x_5082_);
if (v___x_5083_ == 0)
{
uint32_t v___x_5084_; uint8_t v___x_5085_; 
v___x_5084_ = 123;
v___x_5085_ = lean_uint32_dec_eq(v_c_5060_, v___x_5084_);
v___y_5063_ = v___x_5085_;
goto v___jp_5062_;
}
else
{
v___y_5063_ = v___x_5083_;
goto v___jp_5062_;
}
v___jp_5062_:
{
if (v___y_5063_ == 0)
{
uint8_t v___x_5064_; 
v___x_5064_ = lean_string_utf8_at_end(v_s_5057_, v_i_5061_);
if (v___x_5064_ == 0)
{
uint32_t v___x_5065_; uint8_t v___x_5066_; 
v___x_5065_ = 92;
v___x_5066_ = lean_uint32_dec_eq(v_c_5060_, v___x_5065_);
if (v___x_5066_ == 0)
{
lean_object* v___x_5067_; 
v___x_5067_ = lean_string_push(v_acc_5059_, v_c_5060_);
v_i_5058_ = v_i_5061_;
v_acc_5059_ = v___x_5067_;
goto _start;
}
else
{
lean_object* v___x_5069_; 
v___x_5069_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5057_, v_i_5061_);
if (lean_obj_tag(v___x_5069_) == 1)
{
lean_object* v_val_5070_; lean_object* v_fst_5071_; lean_object* v_snd_5072_; uint32_t v___x_5073_; lean_object* v___x_5074_; 
lean_dec(v_i_5061_);
v_val_5070_ = lean_ctor_get(v___x_5069_, 0);
lean_inc(v_val_5070_);
lean_dec_ref_known(v___x_5069_, 1);
v_fst_5071_ = lean_ctor_get(v_val_5070_, 0);
lean_inc(v_fst_5071_);
v_snd_5072_ = lean_ctor_get(v_val_5070_, 1);
lean_inc(v_snd_5072_);
lean_dec(v_val_5070_);
v___x_5073_ = lean_unbox_uint32(v_fst_5071_);
lean_dec(v_fst_5071_);
v___x_5074_ = lean_string_push(v_acc_5059_, v___x_5073_);
v_i_5058_ = v_snd_5072_;
v_acc_5059_ = v___x_5074_;
goto _start;
}
else
{
lean_object* v___x_5076_; 
lean_dec(v___x_5069_);
lean_inc_ref(v_s_5057_);
v___x_5076_ = l_Lean_Syntax_decodeStringGap(v_s_5057_, v_i_5061_);
lean_dec(v_i_5061_);
if (lean_obj_tag(v___x_5076_) == 1)
{
lean_object* v_val_5077_; 
v_val_5077_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_val_5077_);
lean_dec_ref_known(v___x_5076_, 1);
v_i_5058_ = v_val_5077_;
goto _start;
}
else
{
lean_object* v___x_5079_; 
lean_dec(v___x_5076_);
lean_dec_ref(v_acc_5059_);
lean_dec_ref(v_s_5057_);
v___x_5079_ = lean_box(0);
return v___x_5079_;
}
}
}
}
else
{
lean_object* v___x_5080_; 
lean_dec(v_i_5061_);
lean_dec_ref(v_acc_5059_);
lean_dec_ref(v_s_5057_);
v___x_5080_ = lean_box(0);
return v___x_5080_;
}
}
else
{
lean_object* v___x_5081_; 
lean_dec(v_i_5061_);
lean_dec_ref(v_s_5057_);
v___x_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5081_, 0, v_acc_5059_);
return v___x_5081_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5086_){
_start:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___x_5087_ = lean_unsigned_to_nat(1u);
v___x_5088_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5089_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5086_, v___x_5087_, v___x_5088_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5093_){
_start:
{
lean_object* v___x_5094_; lean_object* v___x_5095_; 
v___x_5094_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5095_ = l_Lean_Syntax_isLit_x3f(v___x_5094_, v_stx_5093_);
if (lean_obj_tag(v___x_5095_) == 0)
{
return v___x_5095_;
}
else
{
lean_object* v_val_5096_; lean_object* v___x_5097_; 
v_val_5096_ = lean_ctor_get(v___x_5095_, 0);
lean_inc(v_val_5096_);
lean_dec_ref_known(v___x_5095_, 1);
v___x_5097_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5096_);
return v___x_5097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5098_){
_start:
{
lean_object* v_res_5099_; 
v_res_5099_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5098_);
lean_dec(v_stx_5098_);
return v_res_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5100_){
_start:
{
lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; uint8_t v___x_5105_; 
v___x_5101_ = l_Lean_Syntax_getArgs(v_stx_5100_);
v___x_5102_ = lean_unsigned_to_nat(0u);
v___x_5103_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5104_ = lean_array_get_size(v___x_5101_);
v___x_5105_ = lean_nat_dec_lt(v___x_5102_, v___x_5104_);
if (v___x_5105_ == 0)
{
lean_dec_ref(v___x_5101_);
return v___x_5103_;
}
else
{
lean_object* v___x_5106_; lean_object* v___x_5107_; uint8_t v___x_5108_; 
v___x_5106_ = lean_box(v___x_5105_);
v___x_5107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5107_, 0, v___x_5106_);
lean_ctor_set(v___x_5107_, 1, v___x_5103_);
v___x_5108_ = lean_nat_dec_le(v___x_5104_, v___x_5104_);
if (v___x_5108_ == 0)
{
if (v___x_5105_ == 0)
{
lean_dec_ref_known(v___x_5107_, 2);
lean_dec_ref(v___x_5101_);
return v___x_5103_;
}
else
{
size_t v___x_5109_; size_t v___x_5110_; lean_object* v___x_5111_; lean_object* v_snd_5112_; 
v___x_5109_ = ((size_t)0ULL);
v___x_5110_ = lean_usize_of_nat(v___x_5104_);
v___x_5111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5101_, v___x_5109_, v___x_5110_, v___x_5107_);
lean_dec_ref(v___x_5101_);
v_snd_5112_ = lean_ctor_get(v___x_5111_, 1);
lean_inc(v_snd_5112_);
lean_dec_ref(v___x_5111_);
return v_snd_5112_;
}
}
else
{
size_t v___x_5113_; size_t v___x_5114_; lean_object* v___x_5115_; lean_object* v_snd_5116_; 
v___x_5113_ = ((size_t)0ULL);
v___x_5114_ = lean_usize_of_nat(v___x_5104_);
v___x_5115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5101_, v___x_5113_, v___x_5114_, v___x_5107_);
lean_dec_ref(v___x_5101_);
v_snd_5116_ = lean_ctor_get(v___x_5115_, 1);
lean_inc(v_snd_5116_);
lean_dec_ref(v___x_5115_);
return v_snd_5116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5117_){
_start:
{
lean_object* v_res_5118_; 
v_res_5118_ = l_Lean_Syntax_getSepArgs(v_stx_5117_);
lean_dec(v_stx_5117_);
return v_res_5118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5119_, lean_object* v_mkElem_5120_, lean_object* v_mkLit_5121_, lean_object* v_as_5122_, size_t v_sz_5123_, size_t v_i_5124_, lean_object* v_b_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_){
_start:
{
lean_object* v_a_5129_; lean_object* v_a_5130_; lean_object* v_elem_5135_; lean_object* v___y_5136_; lean_object* v___y_5137_; uint8_t v___x_5142_; 
v___x_5142_ = lean_usize_dec_lt(v_i_5124_, v_sz_5123_);
if (v___x_5142_ == 0)
{
lean_object* v___x_5143_; 
lean_dec_ref(v_mkLit_5121_);
lean_dec_ref(v_mkElem_5120_);
lean_dec_ref(v_mkAppend_5119_);
v___x_5143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5143_, 0, v_b_5125_);
lean_ctor_set(v___x_5143_, 1, v___y_5127_);
return v___x_5143_;
}
else
{
lean_object* v_a_5144_; lean_object* v___x_5145_; 
v_a_5144_ = lean_array_uget_borrowed(v_as_5122_, v_i_5124_);
v___x_5145_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5144_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_methods_5146_; lean_object* v_quotContext_5147_; lean_object* v_currMacroScope_5148_; lean_object* v_currRecDepth_5149_; lean_object* v_maxRecDepth_5150_; lean_object* v_ref_5151_; lean_object* v_ref_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; 
v_methods_5146_ = lean_ctor_get(v___y_5126_, 0);
v_quotContext_5147_ = lean_ctor_get(v___y_5126_, 1);
v_currMacroScope_5148_ = lean_ctor_get(v___y_5126_, 2);
v_currRecDepth_5149_ = lean_ctor_get(v___y_5126_, 3);
v_maxRecDepth_5150_ = lean_ctor_get(v___y_5126_, 4);
v_ref_5151_ = lean_ctor_get(v___y_5126_, 5);
v_ref_5152_ = l_Lean_replaceRef(v_a_5144_, v_ref_5151_);
lean_inc(v_maxRecDepth_5150_);
lean_inc(v_currRecDepth_5149_);
lean_inc(v_currMacroScope_5148_);
lean_inc(v_quotContext_5147_);
lean_inc(v_methods_5146_);
v___x_5153_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5153_, 0, v_methods_5146_);
lean_ctor_set(v___x_5153_, 1, v_quotContext_5147_);
lean_ctor_set(v___x_5153_, 2, v_currMacroScope_5148_);
lean_ctor_set(v___x_5153_, 3, v_currRecDepth_5149_);
lean_ctor_set(v___x_5153_, 4, v_maxRecDepth_5150_);
lean_ctor_set(v___x_5153_, 5, v_ref_5152_);
lean_inc_ref(v_mkElem_5120_);
lean_inc(v_a_5144_);
v___x_5154_ = lean_apply_3(v_mkElem_5120_, v_a_5144_, v___x_5153_, v___y_5127_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_object* v_a_5155_; lean_object* v_a_5156_; 
v_a_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_a_5155_);
v_a_5156_ = lean_ctor_get(v___x_5154_, 1);
lean_inc(v_a_5156_);
lean_dec_ref_known(v___x_5154_, 2);
v_elem_5135_ = v_a_5155_;
v___y_5136_ = v___y_5126_;
v___y_5137_ = v_a_5156_;
goto v___jp_5134_;
}
else
{
lean_dec(v_b_5125_);
lean_dec_ref(v_mkLit_5121_);
lean_dec_ref(v_mkElem_5120_);
lean_dec_ref(v_mkAppend_5119_);
return v___x_5154_;
}
}
else
{
lean_object* v_val_5157_; uint8_t v___x_5158_; 
v_val_5157_ = lean_ctor_get(v___x_5145_, 0);
lean_inc_n(v_val_5157_, 2);
lean_dec_ref_known(v___x_5145_, 1);
v___x_5158_ = lean_string_isempty(v_val_5157_);
if (v___x_5158_ == 0)
{
lean_object* v_methods_5159_; lean_object* v_quotContext_5160_; lean_object* v_currMacroScope_5161_; lean_object* v_currRecDepth_5162_; lean_object* v_maxRecDepth_5163_; lean_object* v_ref_5164_; lean_object* v_ref_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; 
v_methods_5159_ = lean_ctor_get(v___y_5126_, 0);
v_quotContext_5160_ = lean_ctor_get(v___y_5126_, 1);
v_currMacroScope_5161_ = lean_ctor_get(v___y_5126_, 2);
v_currRecDepth_5162_ = lean_ctor_get(v___y_5126_, 3);
v_maxRecDepth_5163_ = lean_ctor_get(v___y_5126_, 4);
v_ref_5164_ = lean_ctor_get(v___y_5126_, 5);
v_ref_5165_ = l_Lean_replaceRef(v_a_5144_, v_ref_5164_);
lean_inc(v_maxRecDepth_5163_);
lean_inc(v_currRecDepth_5162_);
lean_inc(v_currMacroScope_5161_);
lean_inc(v_quotContext_5160_);
lean_inc(v_methods_5159_);
v___x_5166_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5166_, 0, v_methods_5159_);
lean_ctor_set(v___x_5166_, 1, v_quotContext_5160_);
lean_ctor_set(v___x_5166_, 2, v_currMacroScope_5161_);
lean_ctor_set(v___x_5166_, 3, v_currRecDepth_5162_);
lean_ctor_set(v___x_5166_, 4, v_maxRecDepth_5163_);
lean_ctor_set(v___x_5166_, 5, v_ref_5165_);
lean_inc_ref(v_mkLit_5121_);
v___x_5167_ = lean_apply_3(v_mkLit_5121_, v_val_5157_, v___x_5166_, v___y_5127_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; lean_object* v_a_5169_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
lean_inc(v_a_5168_);
v_a_5169_ = lean_ctor_get(v___x_5167_, 1);
lean_inc(v_a_5169_);
lean_dec_ref_known(v___x_5167_, 2);
v_elem_5135_ = v_a_5168_;
v___y_5136_ = v___y_5126_;
v___y_5137_ = v_a_5169_;
goto v___jp_5134_;
}
else
{
lean_dec(v_b_5125_);
lean_dec_ref(v_mkLit_5121_);
lean_dec_ref(v_mkElem_5120_);
lean_dec_ref(v_mkAppend_5119_);
return v___x_5167_;
}
}
else
{
lean_dec(v_val_5157_);
v_a_5129_ = v_b_5125_;
v_a_5130_ = v___y_5127_;
goto v___jp_5128_;
}
}
}
v___jp_5128_:
{
size_t v___x_5131_; size_t v___x_5132_; 
v___x_5131_ = ((size_t)1ULL);
v___x_5132_ = lean_usize_add(v_i_5124_, v___x_5131_);
v_i_5124_ = v___x_5132_;
v_b_5125_ = v_a_5129_;
v___y_5127_ = v_a_5130_;
goto _start;
}
v___jp_5134_:
{
uint8_t v___x_5138_; 
v___x_5138_ = l_Lean_Syntax_isMissing(v_b_5125_);
if (v___x_5138_ == 0)
{
lean_object* v___x_5139_; 
lean_inc_ref(v_mkAppend_5119_);
lean_inc_ref(v___y_5136_);
v___x_5139_ = lean_apply_4(v_mkAppend_5119_, v_b_5125_, v_elem_5135_, v___y_5136_, v___y_5137_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v_a_5140_; lean_object* v_a_5141_; 
v_a_5140_ = lean_ctor_get(v___x_5139_, 0);
lean_inc(v_a_5140_);
v_a_5141_ = lean_ctor_get(v___x_5139_, 1);
lean_inc(v_a_5141_);
lean_dec_ref_known(v___x_5139_, 2);
v_a_5129_ = v_a_5140_;
v_a_5130_ = v_a_5141_;
goto v___jp_5128_;
}
else
{
lean_dec_ref(v_mkLit_5121_);
lean_dec_ref(v_mkElem_5120_);
lean_dec_ref(v_mkAppend_5119_);
return v___x_5139_;
}
}
else
{
lean_dec(v_b_5125_);
v_a_5129_ = v_elem_5135_;
v_a_5130_ = v___y_5137_;
goto v___jp_5128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5170_, lean_object* v_mkElem_5171_, lean_object* v_mkLit_5172_, lean_object* v_as_5173_, lean_object* v_sz_5174_, lean_object* v_i_5175_, lean_object* v_b_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_){
_start:
{
size_t v_sz_boxed_5179_; size_t v_i_boxed_5180_; lean_object* v_res_5181_; 
v_sz_boxed_5179_ = lean_unbox_usize(v_sz_5174_);
lean_dec(v_sz_5174_);
v_i_boxed_5180_ = lean_unbox_usize(v_i_5175_);
lean_dec(v_i_5175_);
v_res_5181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5170_, v_mkElem_5171_, v_mkLit_5172_, v_as_5173_, v_sz_boxed_5179_, v_i_boxed_5180_, v_b_5176_, v___y_5177_, v___y_5178_);
lean_dec_ref(v___y_5177_);
lean_dec_ref(v_as_5173_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5182_, lean_object* v_mkAppend_5183_, lean_object* v_mkElem_5184_, lean_object* v_mkLit_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_){
_start:
{
lean_object* v_result_5188_; size_t v_sz_5189_; size_t v___x_5190_; lean_object* v___x_5191_; 
v_result_5188_ = lean_box(0);
v_sz_5189_ = lean_array_size(v_chunks_5182_);
v___x_5190_ = ((size_t)0ULL);
lean_inc_ref(v_mkLit_5185_);
v___x_5191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5183_, v_mkElem_5184_, v_mkLit_5185_, v_chunks_5182_, v_sz_5189_, v___x_5190_, v_result_5188_, v_a_5186_, v_a_5187_);
if (lean_obj_tag(v___x_5191_) == 0)
{
lean_object* v_a_5192_; lean_object* v_a_5193_; uint8_t v___x_5194_; 
v_a_5192_ = lean_ctor_get(v___x_5191_, 0);
lean_inc(v_a_5192_);
v_a_5193_ = lean_ctor_get(v___x_5191_, 1);
lean_inc(v_a_5193_);
v___x_5194_ = l_Lean_Syntax_isMissing(v_a_5192_);
lean_dec(v_a_5192_);
if (v___x_5194_ == 0)
{
lean_dec(v_a_5193_);
lean_dec_ref(v_mkLit_5185_);
return v___x_5191_;
}
else
{
lean_object* v___x_5195_; lean_object* v___x_5196_; 
lean_dec_ref_known(v___x_5191_, 2);
v___x_5195_ = ((lean_object*)(l_Lean_versionString___closed__0));
lean_inc_ref(v_a_5186_);
v___x_5196_ = lean_apply_3(v_mkLit_5185_, v___x_5195_, v_a_5186_, v_a_5193_);
return v___x_5196_;
}
}
else
{
lean_dec_ref(v_mkLit_5185_);
return v___x_5191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5197_, lean_object* v_mkAppend_5198_, lean_object* v_mkElem_5199_, lean_object* v_mkLit_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_){
_start:
{
lean_object* v_res_5203_; 
v_res_5203_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5197_, v_mkAppend_5198_, v_mkElem_5199_, v_mkLit_5200_, v_a_5201_, v_a_5202_);
lean_dec_ref(v_a_5201_);
lean_dec_ref(v_chunks_5197_);
return v_res_5203_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5208_, lean_object* v_b_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_){
_start:
{
lean_object* v_ref_5212_; uint8_t v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; 
v_ref_5212_ = lean_ctor_get(v___y_5210_, 5);
v___x_5213_ = 0;
v___x_5214_ = l_Lean_SourceInfo_fromRef(v_ref_5212_, v___x_5213_);
v___x_5215_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5216_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5214_);
v___x_5217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5217_, 0, v___x_5214_);
lean_ctor_set(v___x_5217_, 1, v___x_5216_);
v___x_5218_ = l_Lean_Syntax_node3(v___x_5214_, v___x_5215_, v_a_5208_, v___x_5217_, v_b_5209_);
v___x_5219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5219_, 0, v___x_5218_);
lean_ctor_set(v___x_5219_, 1, v___y_5211_);
return v___x_5219_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5220_, lean_object* v_b_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_){
_start:
{
lean_object* v_res_5224_; 
v_res_5224_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5220_, v_b_5221_, v___y_5222_, v___y_5223_);
lean_dec_ref(v___y_5222_);
return v_res_5224_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5225_, lean_object* v_a_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_){
_start:
{
lean_object* v_ref_5229_; uint8_t v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
v_ref_5229_ = lean_ctor_get(v___y_5227_, 5);
v___x_5230_ = 0;
v___x_5231_ = l_Lean_SourceInfo_fromRef(v_ref_5229_, v___x_5230_);
v___x_5232_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5233_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5231_);
v___x_5234_ = l_Lean_Syntax_node1(v___x_5231_, v___x_5233_, v_a_5226_);
v___x_5235_ = l_Lean_Syntax_node2(v___x_5231_, v___x_5232_, v_ofInterpFn_5225_, v___x_5234_);
v___x_5236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5236_, 0, v___x_5235_);
lean_ctor_set(v___x_5236_, 1, v___y_5228_);
return v___x_5236_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5237_, lean_object* v_a_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_){
_start:
{
lean_object* v_res_5241_; 
v_res_5241_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5237_, v_a_5238_, v___y_5239_, v___y_5240_);
lean_dec_ref(v___y_5239_);
return v_res_5241_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5242_, lean_object* v_s_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
lean_object* v_ref_5246_; uint8_t v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; 
v_ref_5246_ = lean_ctor_get(v___y_5244_, 5);
v___x_5247_ = 0;
v___x_5248_ = l_Lean_SourceInfo_fromRef(v_ref_5246_, v___x_5247_);
v___x_5249_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5250_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5251_ = lean_box(2);
v___x_5252_ = l_Lean_Syntax_mkStrLit(v_s_5243_, v___x_5251_);
lean_inc(v___x_5248_);
v___x_5253_ = l_Lean_Syntax_node1(v___x_5248_, v___x_5250_, v___x_5252_);
v___x_5254_ = l_Lean_Syntax_node2(v___x_5248_, v___x_5249_, v_ofLitFn_5242_, v___x_5253_);
v___x_5255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5255_, 0, v___x_5254_);
lean_ctor_set(v___x_5255_, 1, v___y_5245_);
return v___x_5255_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5256_, lean_object* v_s_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_){
_start:
{
lean_object* v_res_5260_; 
v_res_5260_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5256_, v_s_5257_, v___y_5258_, v___y_5259_);
lean_dec_ref(v___y_5258_);
return v_res_5260_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5278_; lean_object* v___x_5279_; 
v___x_5278_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5279_ = l_String_toRawSubstring_x27(v___x_5278_);
return v___x_5279_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5300_, lean_object* v_type_5301_, lean_object* v_ofInterpFn_5302_, lean_object* v_ofLitFn_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_){
_start:
{
lean_object* v___f_5306_; lean_object* v___f_5307_; lean_object* v___f_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; 
v___f_5306_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5307_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5307_, 0, v_ofInterpFn_5302_);
v___f_5308_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5308_, 0, v_ofLitFn_5303_);
v___x_5309_ = l_Lean_Syntax_getArgs(v_interpStr_5300_);
v___x_5310_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5309_, v___f_5306_, v___f_5307_, v___f_5308_, v_a_5304_, v_a_5305_);
lean_dec_ref(v___x_5309_);
if (lean_obj_tag(v___x_5310_) == 0)
{
lean_object* v_a_5311_; lean_object* v_a_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5343_; 
v_a_5311_ = lean_ctor_get(v___x_5310_, 0);
v_a_5312_ = lean_ctor_get(v___x_5310_, 1);
v_isSharedCheck_5343_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5314_ = v___x_5310_;
v_isShared_5315_ = v_isSharedCheck_5343_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_a_5312_);
lean_inc(v_a_5311_);
lean_dec(v___x_5310_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5343_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v_quotContext_5316_; lean_object* v_currMacroScope_5317_; lean_object* v_ref_5318_; uint8_t v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5341_; 
v_quotContext_5316_ = lean_ctor_get(v_a_5304_, 1);
v_currMacroScope_5317_ = lean_ctor_get(v_a_5304_, 2);
v_ref_5318_ = lean_ctor_get(v_a_5304_, 5);
v___x_5319_ = 0;
v___x_5320_ = l_Lean_SourceInfo_fromRef(v_ref_5318_, v___x_5319_);
v___x_5321_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5322_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5323_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc_n(v___x_5320_, 7);
v___x_5324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5324_, 0, v___x_5320_);
lean_ctor_set(v___x_5324_, 1, v___x_5323_);
v___x_5325_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5326_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5327_ = lean_box(0);
lean_inc(v_currMacroScope_5317_);
lean_inc(v_quotContext_5316_);
v___x_5328_ = l_Lean_addMacroScope(v_quotContext_5316_, v___x_5327_, v_currMacroScope_5317_);
v___x_5329_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
v___x_5330_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5330_, 0, v___x_5320_);
lean_ctor_set(v___x_5330_, 1, v___x_5326_);
lean_ctor_set(v___x_5330_, 2, v___x_5328_);
lean_ctor_set(v___x_5330_, 3, v___x_5329_);
v___x_5331_ = l_Lean_Syntax_node1(v___x_5320_, v___x_5325_, v___x_5330_);
v___x_5332_ = l_Lean_Syntax_node2(v___x_5320_, v___x_5322_, v___x_5324_, v___x_5331_);
v___x_5333_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_5334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5334_, 0, v___x_5320_);
lean_ctor_set(v___x_5334_, 1, v___x_5333_);
v___x_5335_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5336_ = l_Lean_Syntax_node1(v___x_5320_, v___x_5335_, v_type_5301_);
v___x_5337_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
v___x_5338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5338_, 0, v___x_5320_);
lean_ctor_set(v___x_5338_, 1, v___x_5337_);
v___x_5339_ = l_Lean_Syntax_node5(v___x_5320_, v___x_5321_, v___x_5332_, v_a_5311_, v___x_5334_, v___x_5336_, v___x_5338_);
if (v_isShared_5315_ == 0)
{
lean_ctor_set(v___x_5314_, 0, v___x_5339_);
v___x_5341_ = v___x_5314_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v___x_5339_);
lean_ctor_set(v_reuseFailAlloc_5342_, 1, v_a_5312_);
v___x_5341_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
return v___x_5341_;
}
}
}
else
{
lean_object* v_a_5344_; lean_object* v_a_5345_; lean_object* v___x_5347_; uint8_t v_isShared_5348_; uint8_t v_isSharedCheck_5352_; 
lean_dec(v_type_5301_);
v_a_5344_ = lean_ctor_get(v___x_5310_, 0);
v_a_5345_ = lean_ctor_get(v___x_5310_, 1);
v_isSharedCheck_5352_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5352_ == 0)
{
v___x_5347_ = v___x_5310_;
v_isShared_5348_ = v_isSharedCheck_5352_;
goto v_resetjp_5346_;
}
else
{
lean_inc(v_a_5345_);
lean_inc(v_a_5344_);
lean_dec(v___x_5310_);
v___x_5347_ = lean_box(0);
v_isShared_5348_ = v_isSharedCheck_5352_;
goto v_resetjp_5346_;
}
v_resetjp_5346_:
{
lean_object* v___x_5350_; 
if (v_isShared_5348_ == 0)
{
v___x_5350_ = v___x_5347_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v_a_5344_);
lean_ctor_set(v_reuseFailAlloc_5351_, 1, v_a_5345_);
v___x_5350_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
return v___x_5350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5353_, lean_object* v_type_5354_, lean_object* v_ofInterpFn_5355_, lean_object* v_ofLitFn_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_){
_start:
{
lean_object* v_res_5359_; 
v_res_5359_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5353_, v_type_5354_, v_ofInterpFn_5355_, v_ofLitFn_5356_, v_a_5357_, v_a_5358_);
lean_dec_ref(v_a_5357_);
lean_dec(v_interpStr_5353_);
return v_res_5359_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5360_){
_start:
{
lean_object* v___x_5361_; lean_object* v___x_5362_; 
v___x_5361_ = lean_unsigned_to_nat(1u);
v___x_5362_ = l_Lean_Syntax_getArg(v_stx_5360_, v___x_5361_);
if (lean_obj_tag(v___x_5362_) == 2)
{
lean_object* v_val_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; 
v_val_5363_ = lean_ctor_get(v___x_5362_, 1);
lean_inc_ref(v_val_5363_);
lean_dec_ref_known(v___x_5362_, 2);
v___x_5364_ = lean_unsigned_to_nat(0u);
v___x_5365_ = lean_string_utf8_byte_size(v_val_5363_);
v___x_5366_ = lean_unsigned_to_nat(2u);
v___x_5367_ = lean_string_pos_sub(v___x_5365_, v___x_5366_);
v___x_5368_ = lean_string_utf8_extract(v_val_5363_, v___x_5364_, v___x_5367_);
lean_dec(v___x_5367_);
lean_dec_ref(v_val_5363_);
return v___x_5368_;
}
else
{
lean_object* v___x_5369_; 
lean_dec(v___x_5362_);
v___x_5369_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* v_stx_5370_){
_start:
{
lean_object* v_res_5371_; 
v_res_5371_ = l_Lean_TSyntax_getDocString(v_stx_5370_);
lean_dec(v_stx_5370_);
return v_res_5371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5390_, lean_object* v_prec_5391_){
_start:
{
lean_object* v___y_5393_; lean_object* v___y_5400_; lean_object* v___y_5407_; lean_object* v___y_5414_; lean_object* v___y_5421_; lean_object* v___y_5428_; 
switch(v_x_5390_)
{
case 0:
{
lean_object* v___x_5434_; uint8_t v___x_5435_; 
v___x_5434_ = lean_unsigned_to_nat(1024u);
v___x_5435_ = lean_nat_dec_le(v___x_5434_, v_prec_5391_);
if (v___x_5435_ == 0)
{
lean_object* v___x_5436_; 
v___x_5436_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5393_ = v___x_5436_;
goto v___jp_5392_;
}
else
{
lean_object* v___x_5437_; 
v___x_5437_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5393_ = v___x_5437_;
goto v___jp_5392_;
}
}
case 1:
{
lean_object* v___x_5438_; uint8_t v___x_5439_; 
v___x_5438_ = lean_unsigned_to_nat(1024u);
v___x_5439_ = lean_nat_dec_le(v___x_5438_, v_prec_5391_);
if (v___x_5439_ == 0)
{
lean_object* v___x_5440_; 
v___x_5440_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5400_ = v___x_5440_;
goto v___jp_5399_;
}
else
{
lean_object* v___x_5441_; 
v___x_5441_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5400_ = v___x_5441_;
goto v___jp_5399_;
}
}
case 2:
{
lean_object* v___x_5442_; uint8_t v___x_5443_; 
v___x_5442_ = lean_unsigned_to_nat(1024u);
v___x_5443_ = lean_nat_dec_le(v___x_5442_, v_prec_5391_);
if (v___x_5443_ == 0)
{
lean_object* v___x_5444_; 
v___x_5444_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5407_ = v___x_5444_;
goto v___jp_5406_;
}
else
{
lean_object* v___x_5445_; 
v___x_5445_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5407_ = v___x_5445_;
goto v___jp_5406_;
}
}
case 3:
{
lean_object* v___x_5446_; uint8_t v___x_5447_; 
v___x_5446_ = lean_unsigned_to_nat(1024u);
v___x_5447_ = lean_nat_dec_le(v___x_5446_, v_prec_5391_);
if (v___x_5447_ == 0)
{
lean_object* v___x_5448_; 
v___x_5448_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5414_ = v___x_5448_;
goto v___jp_5413_;
}
else
{
lean_object* v___x_5449_; 
v___x_5449_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5414_ = v___x_5449_;
goto v___jp_5413_;
}
}
case 4:
{
lean_object* v___x_5450_; uint8_t v___x_5451_; 
v___x_5450_ = lean_unsigned_to_nat(1024u);
v___x_5451_ = lean_nat_dec_le(v___x_5450_, v_prec_5391_);
if (v___x_5451_ == 0)
{
lean_object* v___x_5452_; 
v___x_5452_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5421_ = v___x_5452_;
goto v___jp_5420_;
}
else
{
lean_object* v___x_5453_; 
v___x_5453_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5421_ = v___x_5453_;
goto v___jp_5420_;
}
}
default: 
{
lean_object* v___x_5454_; uint8_t v___x_5455_; 
v___x_5454_ = lean_unsigned_to_nat(1024u);
v___x_5455_ = lean_nat_dec_le(v___x_5454_, v_prec_5391_);
if (v___x_5455_ == 0)
{
lean_object* v___x_5456_; 
v___x_5456_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5428_ = v___x_5456_;
goto v___jp_5427_;
}
else
{
lean_object* v___x_5457_; 
v___x_5457_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5428_ = v___x_5457_;
goto v___jp_5427_;
}
}
}
v___jp_5392_:
{
lean_object* v___x_5394_; lean_object* v___x_5395_; uint8_t v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; 
v___x_5394_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
lean_inc(v___y_5393_);
v___x_5395_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5395_, 0, v___y_5393_);
lean_ctor_set(v___x_5395_, 1, v___x_5394_);
v___x_5396_ = 0;
v___x_5397_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5397_, 0, v___x_5395_);
lean_ctor_set_uint8(v___x_5397_, sizeof(void*)*1, v___x_5396_);
v___x_5398_ = l_Repr_addAppParen(v___x_5397_, v_prec_5391_);
return v___x_5398_;
}
v___jp_5399_:
{
lean_object* v___x_5401_; lean_object* v___x_5402_; uint8_t v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; 
v___x_5401_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__3));
lean_inc(v___y_5400_);
v___x_5402_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5402_, 0, v___y_5400_);
lean_ctor_set(v___x_5402_, 1, v___x_5401_);
v___x_5403_ = 0;
v___x_5404_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5404_, 0, v___x_5402_);
lean_ctor_set_uint8(v___x_5404_, sizeof(void*)*1, v___x_5403_);
v___x_5405_ = l_Repr_addAppParen(v___x_5404_, v_prec_5391_);
return v___x_5405_;
}
v___jp_5406_:
{
lean_object* v___x_5408_; lean_object* v___x_5409_; uint8_t v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; 
v___x_5408_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__5));
lean_inc(v___y_5407_);
v___x_5409_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5409_, 0, v___y_5407_);
lean_ctor_set(v___x_5409_, 1, v___x_5408_);
v___x_5410_ = 0;
v___x_5411_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5411_, 0, v___x_5409_);
lean_ctor_set_uint8(v___x_5411_, sizeof(void*)*1, v___x_5410_);
v___x_5412_ = l_Repr_addAppParen(v___x_5411_, v_prec_5391_);
return v___x_5412_;
}
v___jp_5413_:
{
lean_object* v___x_5415_; lean_object* v___x_5416_; uint8_t v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5415_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__7));
lean_inc(v___y_5414_);
v___x_5416_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5416_, 0, v___y_5414_);
lean_ctor_set(v___x_5416_, 1, v___x_5415_);
v___x_5417_ = 0;
v___x_5418_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5418_, 0, v___x_5416_);
lean_ctor_set_uint8(v___x_5418_, sizeof(void*)*1, v___x_5417_);
v___x_5419_ = l_Repr_addAppParen(v___x_5418_, v_prec_5391_);
return v___x_5419_;
}
v___jp_5420_:
{
lean_object* v___x_5422_; lean_object* v___x_5423_; uint8_t v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; 
v___x_5422_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__9));
lean_inc(v___y_5421_);
v___x_5423_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5423_, 0, v___y_5421_);
lean_ctor_set(v___x_5423_, 1, v___x_5422_);
v___x_5424_ = 0;
v___x_5425_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5425_, 0, v___x_5423_);
lean_ctor_set_uint8(v___x_5425_, sizeof(void*)*1, v___x_5424_);
v___x_5426_ = l_Repr_addAppParen(v___x_5425_, v_prec_5391_);
return v___x_5426_;
}
v___jp_5427_:
{
lean_object* v___x_5429_; lean_object* v___x_5430_; uint8_t v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; 
v___x_5429_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__11));
lean_inc(v___y_5428_);
v___x_5430_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5430_, 0, v___y_5428_);
lean_ctor_set(v___x_5430_, 1, v___x_5429_);
v___x_5431_ = 0;
v___x_5432_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5432_, 0, v___x_5430_);
lean_ctor_set_uint8(v___x_5432_, sizeof(void*)*1, v___x_5431_);
v___x_5433_ = l_Repr_addAppParen(v___x_5432_, v_prec_5391_);
return v___x_5433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5458_, lean_object* v_prec_5459_){
_start:
{
uint8_t v_x_341__boxed_5460_; lean_object* v_res_5461_; 
v_x_341__boxed_5460_ = lean_unbox(v_x_5458_);
v_res_5461_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_341__boxed_5460_, v_prec_5459_);
lean_dec(v_prec_5459_);
return v_res_5461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5473_, lean_object* v_prec_5474_){
_start:
{
lean_object* v___y_5476_; lean_object* v___y_5483_; lean_object* v___y_5490_; 
switch(v_x_5473_)
{
case 0:
{
lean_object* v___x_5496_; uint8_t v___x_5497_; 
v___x_5496_ = lean_unsigned_to_nat(1024u);
v___x_5497_ = lean_nat_dec_le(v___x_5496_, v_prec_5474_);
if (v___x_5497_ == 0)
{
lean_object* v___x_5498_; 
v___x_5498_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5476_ = v___x_5498_;
goto v___jp_5475_;
}
else
{
lean_object* v___x_5499_; 
v___x_5499_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5476_ = v___x_5499_;
goto v___jp_5475_;
}
}
case 1:
{
lean_object* v___x_5500_; uint8_t v___x_5501_; 
v___x_5500_ = lean_unsigned_to_nat(1024u);
v___x_5501_ = lean_nat_dec_le(v___x_5500_, v_prec_5474_);
if (v___x_5501_ == 0)
{
lean_object* v___x_5502_; 
v___x_5502_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5483_ = v___x_5502_;
goto v___jp_5482_;
}
else
{
lean_object* v___x_5503_; 
v___x_5503_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5483_ = v___x_5503_;
goto v___jp_5482_;
}
}
default: 
{
lean_object* v___x_5504_; uint8_t v___x_5505_; 
v___x_5504_ = lean_unsigned_to_nat(1024u);
v___x_5505_ = lean_nat_dec_le(v___x_5504_, v_prec_5474_);
if (v___x_5505_ == 0)
{
lean_object* v___x_5506_; 
v___x_5506_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5490_ = v___x_5506_;
goto v___jp_5489_;
}
else
{
lean_object* v___x_5507_; 
v___x_5507_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5490_ = v___x_5507_;
goto v___jp_5489_;
}
}
}
v___jp_5475_:
{
lean_object* v___x_5477_; lean_object* v___x_5478_; uint8_t v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; 
v___x_5477_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
lean_inc(v___y_5476_);
v___x_5478_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5478_, 0, v___y_5476_);
lean_ctor_set(v___x_5478_, 1, v___x_5477_);
v___x_5479_ = 0;
v___x_5480_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5480_, 0, v___x_5478_);
lean_ctor_set_uint8(v___x_5480_, sizeof(void*)*1, v___x_5479_);
v___x_5481_ = l_Repr_addAppParen(v___x_5480_, v_prec_5474_);
return v___x_5481_;
}
v___jp_5482_:
{
lean_object* v___x_5484_; lean_object* v___x_5485_; uint8_t v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; 
v___x_5484_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
lean_inc(v___y_5483_);
v___x_5485_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5485_, 0, v___y_5483_);
lean_ctor_set(v___x_5485_, 1, v___x_5484_);
v___x_5486_ = 0;
v___x_5487_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5487_, 0, v___x_5485_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*1, v___x_5486_);
v___x_5488_ = l_Repr_addAppParen(v___x_5487_, v_prec_5474_);
return v___x_5488_;
}
v___jp_5489_:
{
lean_object* v___x_5491_; lean_object* v___x_5492_; uint8_t v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5491_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
lean_inc(v___y_5490_);
v___x_5492_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5492_, 0, v___y_5490_);
lean_ctor_set(v___x_5492_, 1, v___x_5491_);
v___x_5493_ = 0;
v___x_5494_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5494_, 0, v___x_5492_);
lean_ctor_set_uint8(v___x_5494_, sizeof(void*)*1, v___x_5493_);
v___x_5495_ = l_Repr_addAppParen(v___x_5494_, v_prec_5474_);
return v___x_5495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5508_, lean_object* v_prec_5509_){
_start:
{
uint8_t v_x_173__boxed_5510_; lean_object* v_res_5511_; 
v_x_173__boxed_5510_ = lean_unbox(v_x_5508_);
v_res_5511_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_173__boxed_5510_, v_prec_5509_);
lean_dec(v_prec_5509_);
return v_res_5511_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5523_; lean_object* v___x_5524_; 
v___x_5523_ = lean_unsigned_to_nat(8u);
v___x_5524_ = lean_nat_to_int(v___x_5523_);
return v___x_5524_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5534_; lean_object* v___x_5535_; 
v___x_5534_ = lean_unsigned_to_nat(13u);
v___x_5535_ = lean_nat_to_int(v___x_5534_);
return v___x_5535_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5545_; lean_object* v___x_5546_; 
v___x_5545_ = lean_unsigned_to_nat(10u);
v___x_5546_ = lean_nat_to_int(v___x_5545_);
return v___x_5546_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5550_; lean_object* v___x_5551_; 
v___x_5550_ = lean_unsigned_to_nat(14u);
v___x_5551_ = lean_nat_to_int(v___x_5550_);
return v___x_5551_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5555_; lean_object* v___x_5556_; 
v___x_5555_ = lean_unsigned_to_nat(19u);
v___x_5556_ = lean_nat_to_int(v___x_5555_);
return v___x_5556_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5560_; lean_object* v___x_5561_; 
v___x_5560_ = lean_unsigned_to_nat(20u);
v___x_5561_ = lean_nat_to_int(v___x_5560_);
return v___x_5561_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5568_; lean_object* v___x_5569_; 
v___x_5568_ = lean_unsigned_to_nat(9u);
v___x_5569_ = lean_nat_to_int(v___x_5568_);
return v___x_5569_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5576_; lean_object* v___x_5577_; 
v___x_5576_ = lean_unsigned_to_nat(12u);
v___x_5577_ = lean_nat_to_int(v___x_5576_);
return v___x_5577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5584_){
_start:
{
uint8_t v_zeta_5585_; uint8_t v_beta_5586_; uint8_t v_eta_5587_; uint8_t v_etaStruct_5588_; uint8_t v_iota_5589_; uint8_t v_proj_5590_; uint8_t v_decide_5591_; uint8_t v_autoUnfold_5592_; uint8_t v_failIfUnchanged_5593_; uint8_t v_unfoldPartialApp_5594_; uint8_t v_zetaDelta_5595_; uint8_t v_index_5596_; uint8_t v_zetaUnused_5597_; uint8_t v_zetaHave_5598_; uint8_t v_locals_5599_; uint8_t v_instances_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; uint8_t v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; 
v_zeta_5585_ = lean_ctor_get_uint8(v_x_5584_, 0);
v_beta_5586_ = lean_ctor_get_uint8(v_x_5584_, 1);
v_eta_5587_ = lean_ctor_get_uint8(v_x_5584_, 2);
v_etaStruct_5588_ = lean_ctor_get_uint8(v_x_5584_, 3);
v_iota_5589_ = lean_ctor_get_uint8(v_x_5584_, 4);
v_proj_5590_ = lean_ctor_get_uint8(v_x_5584_, 5);
v_decide_5591_ = lean_ctor_get_uint8(v_x_5584_, 6);
v_autoUnfold_5592_ = lean_ctor_get_uint8(v_x_5584_, 7);
v_failIfUnchanged_5593_ = lean_ctor_get_uint8(v_x_5584_, 8);
v_unfoldPartialApp_5594_ = lean_ctor_get_uint8(v_x_5584_, 9);
v_zetaDelta_5595_ = lean_ctor_get_uint8(v_x_5584_, 10);
v_index_5596_ = lean_ctor_get_uint8(v_x_5584_, 11);
v_zetaUnused_5597_ = lean_ctor_get_uint8(v_x_5584_, 12);
v_zetaHave_5598_ = lean_ctor_get_uint8(v_x_5584_, 13);
v_locals_5599_ = lean_ctor_get_uint8(v_x_5584_, 14);
v_instances_5600_ = lean_ctor_get_uint8(v_x_5584_, 15);
v___x_5601_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5602_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5603_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5604_ = lean_unsigned_to_nat(0u);
v___x_5605_ = l_Bool_repr___redArg(v_zeta_5585_);
v___x_5606_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5606_, 0, v___x_5603_);
lean_ctor_set(v___x_5606_, 1, v___x_5605_);
v___x_5607_ = 0;
v___x_5608_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5608_, 0, v___x_5606_);
lean_ctor_set_uint8(v___x_5608_, sizeof(void*)*1, v___x_5607_);
v___x_5609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5609_, 0, v___x_5602_);
lean_ctor_set(v___x_5609_, 1, v___x_5608_);
v___x_5610_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5611_, 0, v___x_5609_);
lean_ctor_set(v___x_5611_, 1, v___x_5610_);
v___x_5612_ = lean_box(1);
v___x_5613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5613_, 0, v___x_5611_);
lean_ctor_set(v___x_5613_, 1, v___x_5612_);
v___x_5614_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5615_, 0, v___x_5613_);
lean_ctor_set(v___x_5615_, 1, v___x_5614_);
v___x_5616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5615_);
lean_ctor_set(v___x_5616_, 1, v___x_5601_);
v___x_5617_ = l_Bool_repr___redArg(v_beta_5586_);
v___x_5618_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5618_, 0, v___x_5603_);
lean_ctor_set(v___x_5618_, 1, v___x_5617_);
v___x_5619_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5619_, 0, v___x_5618_);
lean_ctor_set_uint8(v___x_5619_, sizeof(void*)*1, v___x_5607_);
v___x_5620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5620_, 0, v___x_5616_);
lean_ctor_set(v___x_5620_, 1, v___x_5619_);
v___x_5621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5621_, 0, v___x_5620_);
lean_ctor_set(v___x_5621_, 1, v___x_5610_);
v___x_5622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5622_, 0, v___x_5621_);
lean_ctor_set(v___x_5622_, 1, v___x_5612_);
v___x_5623_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5624_, 0, v___x_5622_);
lean_ctor_set(v___x_5624_, 1, v___x_5623_);
v___x_5625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5625_, 0, v___x_5624_);
lean_ctor_set(v___x_5625_, 1, v___x_5601_);
v___x_5626_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5627_ = l_Bool_repr___redArg(v_eta_5587_);
v___x_5628_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5628_, 0, v___x_5626_);
lean_ctor_set(v___x_5628_, 1, v___x_5627_);
v___x_5629_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5629_, 0, v___x_5628_);
lean_ctor_set_uint8(v___x_5629_, sizeof(void*)*1, v___x_5607_);
v___x_5630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5630_, 0, v___x_5625_);
lean_ctor_set(v___x_5630_, 1, v___x_5629_);
v___x_5631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5631_, 0, v___x_5630_);
lean_ctor_set(v___x_5631_, 1, v___x_5610_);
v___x_5632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5632_, 0, v___x_5631_);
lean_ctor_set(v___x_5632_, 1, v___x_5612_);
v___x_5633_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5634_, 0, v___x_5632_);
lean_ctor_set(v___x_5634_, 1, v___x_5633_);
v___x_5635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5635_, 0, v___x_5634_);
lean_ctor_set(v___x_5635_, 1, v___x_5601_);
v___x_5636_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5637_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5588_, v___x_5604_);
v___x_5638_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5638_, 0, v___x_5636_);
lean_ctor_set(v___x_5638_, 1, v___x_5637_);
v___x_5639_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5639_, 0, v___x_5638_);
lean_ctor_set_uint8(v___x_5639_, sizeof(void*)*1, v___x_5607_);
v___x_5640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5640_, 0, v___x_5635_);
lean_ctor_set(v___x_5640_, 1, v___x_5639_);
v___x_5641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5640_);
lean_ctor_set(v___x_5641_, 1, v___x_5610_);
v___x_5642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5642_, 0, v___x_5641_);
lean_ctor_set(v___x_5642_, 1, v___x_5612_);
v___x_5643_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5644_, 0, v___x_5642_);
lean_ctor_set(v___x_5644_, 1, v___x_5643_);
v___x_5645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5644_);
lean_ctor_set(v___x_5645_, 1, v___x_5601_);
v___x_5646_ = l_Bool_repr___redArg(v_iota_5589_);
v___x_5647_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5647_, 0, v___x_5603_);
lean_ctor_set(v___x_5647_, 1, v___x_5646_);
v___x_5648_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5648_, 0, v___x_5647_);
lean_ctor_set_uint8(v___x_5648_, sizeof(void*)*1, v___x_5607_);
v___x_5649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5649_, 0, v___x_5645_);
lean_ctor_set(v___x_5649_, 1, v___x_5648_);
v___x_5650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5650_, 0, v___x_5649_);
lean_ctor_set(v___x_5650_, 1, v___x_5610_);
v___x_5651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5651_, 0, v___x_5650_);
lean_ctor_set(v___x_5651_, 1, v___x_5612_);
v___x_5652_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5653_, 0, v___x_5651_);
lean_ctor_set(v___x_5653_, 1, v___x_5652_);
v___x_5654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5654_, 0, v___x_5653_);
lean_ctor_set(v___x_5654_, 1, v___x_5601_);
v___x_5655_ = l_Bool_repr___redArg(v_proj_5590_);
v___x_5656_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5656_, 0, v___x_5603_);
lean_ctor_set(v___x_5656_, 1, v___x_5655_);
v___x_5657_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5657_, 0, v___x_5656_);
lean_ctor_set_uint8(v___x_5657_, sizeof(void*)*1, v___x_5607_);
v___x_5658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5658_, 0, v___x_5654_);
lean_ctor_set(v___x_5658_, 1, v___x_5657_);
v___x_5659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5659_, 0, v___x_5658_);
lean_ctor_set(v___x_5659_, 1, v___x_5610_);
v___x_5660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5660_, 0, v___x_5659_);
lean_ctor_set(v___x_5660_, 1, v___x_5612_);
v___x_5661_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5662_, 0, v___x_5660_);
lean_ctor_set(v___x_5662_, 1, v___x_5661_);
v___x_5663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5662_);
lean_ctor_set(v___x_5663_, 1, v___x_5601_);
v___x_5664_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5665_ = l_Bool_repr___redArg(v_decide_5591_);
v___x_5666_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5666_, 0, v___x_5664_);
lean_ctor_set(v___x_5666_, 1, v___x_5665_);
v___x_5667_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5667_, 0, v___x_5666_);
lean_ctor_set_uint8(v___x_5667_, sizeof(void*)*1, v___x_5607_);
v___x_5668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5663_);
lean_ctor_set(v___x_5668_, 1, v___x_5667_);
v___x_5669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5669_, 0, v___x_5668_);
lean_ctor_set(v___x_5669_, 1, v___x_5610_);
v___x_5670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5670_, 0, v___x_5669_);
lean_ctor_set(v___x_5670_, 1, v___x_5612_);
v___x_5671_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5672_, 0, v___x_5670_);
lean_ctor_set(v___x_5672_, 1, v___x_5671_);
v___x_5673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5673_, 0, v___x_5672_);
lean_ctor_set(v___x_5673_, 1, v___x_5601_);
v___x_5674_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5675_ = l_Bool_repr___redArg(v_autoUnfold_5592_);
v___x_5676_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5676_, 0, v___x_5674_);
lean_ctor_set(v___x_5676_, 1, v___x_5675_);
v___x_5677_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5677_, 0, v___x_5676_);
lean_ctor_set_uint8(v___x_5677_, sizeof(void*)*1, v___x_5607_);
v___x_5678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5678_, 0, v___x_5673_);
lean_ctor_set(v___x_5678_, 1, v___x_5677_);
v___x_5679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5679_, 0, v___x_5678_);
lean_ctor_set(v___x_5679_, 1, v___x_5610_);
v___x_5680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5680_, 0, v___x_5679_);
lean_ctor_set(v___x_5680_, 1, v___x_5612_);
v___x_5681_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5682_, 0, v___x_5680_);
lean_ctor_set(v___x_5682_, 1, v___x_5681_);
v___x_5683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5683_, 0, v___x_5682_);
lean_ctor_set(v___x_5683_, 1, v___x_5601_);
v___x_5684_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5685_ = l_Bool_repr___redArg(v_failIfUnchanged_5593_);
v___x_5686_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5684_);
lean_ctor_set(v___x_5686_, 1, v___x_5685_);
v___x_5687_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5687_, 0, v___x_5686_);
lean_ctor_set_uint8(v___x_5687_, sizeof(void*)*1, v___x_5607_);
v___x_5688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5683_);
lean_ctor_set(v___x_5688_, 1, v___x_5687_);
v___x_5689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5689_, 0, v___x_5688_);
lean_ctor_set(v___x_5689_, 1, v___x_5610_);
v___x_5690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5690_, 0, v___x_5689_);
lean_ctor_set(v___x_5690_, 1, v___x_5612_);
v___x_5691_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5692_, 0, v___x_5690_);
lean_ctor_set(v___x_5692_, 1, v___x_5691_);
v___x_5693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5693_, 0, v___x_5692_);
lean_ctor_set(v___x_5693_, 1, v___x_5601_);
v___x_5694_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5695_ = l_Bool_repr___redArg(v_unfoldPartialApp_5594_);
v___x_5696_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5696_, 0, v___x_5694_);
lean_ctor_set(v___x_5696_, 1, v___x_5695_);
v___x_5697_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5697_, 0, v___x_5696_);
lean_ctor_set_uint8(v___x_5697_, sizeof(void*)*1, v___x_5607_);
v___x_5698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5693_);
lean_ctor_set(v___x_5698_, 1, v___x_5697_);
v___x_5699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5699_, 0, v___x_5698_);
lean_ctor_set(v___x_5699_, 1, v___x_5610_);
v___x_5700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5699_);
lean_ctor_set(v___x_5700_, 1, v___x_5612_);
v___x_5701_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5702_, 0, v___x_5700_);
lean_ctor_set(v___x_5702_, 1, v___x_5701_);
v___x_5703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5703_, 0, v___x_5702_);
lean_ctor_set(v___x_5703_, 1, v___x_5601_);
v___x_5704_ = l_Bool_repr___redArg(v_zetaDelta_5595_);
v___x_5705_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5705_, 0, v___x_5636_);
lean_ctor_set(v___x_5705_, 1, v___x_5704_);
v___x_5706_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5706_, 0, v___x_5705_);
lean_ctor_set_uint8(v___x_5706_, sizeof(void*)*1, v___x_5607_);
v___x_5707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5707_, 0, v___x_5703_);
lean_ctor_set(v___x_5707_, 1, v___x_5706_);
v___x_5708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5708_, 0, v___x_5707_);
lean_ctor_set(v___x_5708_, 1, v___x_5610_);
v___x_5709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5708_);
lean_ctor_set(v___x_5709_, 1, v___x_5612_);
v___x_5710_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5711_, 0, v___x_5709_);
lean_ctor_set(v___x_5711_, 1, v___x_5710_);
v___x_5712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5712_, 0, v___x_5711_);
lean_ctor_set(v___x_5712_, 1, v___x_5601_);
v___x_5713_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5714_ = l_Bool_repr___redArg(v_index_5596_);
v___x_5715_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5713_);
lean_ctor_set(v___x_5715_, 1, v___x_5714_);
v___x_5716_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5716_, 0, v___x_5715_);
lean_ctor_set_uint8(v___x_5716_, sizeof(void*)*1, v___x_5607_);
v___x_5717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5712_);
lean_ctor_set(v___x_5717_, 1, v___x_5716_);
v___x_5718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5718_, 0, v___x_5717_);
lean_ctor_set(v___x_5718_, 1, v___x_5610_);
v___x_5719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5719_, 0, v___x_5718_);
lean_ctor_set(v___x_5719_, 1, v___x_5612_);
v___x_5720_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5721_, 0, v___x_5719_);
lean_ctor_set(v___x_5721_, 1, v___x_5720_);
v___x_5722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5722_, 0, v___x_5721_);
lean_ctor_set(v___x_5722_, 1, v___x_5601_);
v___x_5723_ = l_Bool_repr___redArg(v_zetaUnused_5597_);
v___x_5724_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5724_, 0, v___x_5674_);
lean_ctor_set(v___x_5724_, 1, v___x_5723_);
v___x_5725_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5725_, 0, v___x_5724_);
lean_ctor_set_uint8(v___x_5725_, sizeof(void*)*1, v___x_5607_);
v___x_5726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5726_, 0, v___x_5722_);
lean_ctor_set(v___x_5726_, 1, v___x_5725_);
v___x_5727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5727_, 0, v___x_5726_);
lean_ctor_set(v___x_5727_, 1, v___x_5610_);
v___x_5728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5727_);
lean_ctor_set(v___x_5728_, 1, v___x_5612_);
v___x_5729_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5728_);
lean_ctor_set(v___x_5730_, 1, v___x_5729_);
v___x_5731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5731_, 0, v___x_5730_);
lean_ctor_set(v___x_5731_, 1, v___x_5601_);
v___x_5732_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5733_ = l_Bool_repr___redArg(v_zetaHave_5598_);
v___x_5734_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5734_, 0, v___x_5732_);
lean_ctor_set(v___x_5734_, 1, v___x_5733_);
v___x_5735_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5735_, 0, v___x_5734_);
lean_ctor_set_uint8(v___x_5735_, sizeof(void*)*1, v___x_5607_);
v___x_5736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5731_);
lean_ctor_set(v___x_5736_, 1, v___x_5735_);
v___x_5737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5737_, 0, v___x_5736_);
lean_ctor_set(v___x_5737_, 1, v___x_5610_);
v___x_5738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5737_);
lean_ctor_set(v___x_5738_, 1, v___x_5612_);
v___x_5739_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5740_, 0, v___x_5738_);
lean_ctor_set(v___x_5740_, 1, v___x_5739_);
v___x_5741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5741_, 0, v___x_5740_);
lean_ctor_set(v___x_5741_, 1, v___x_5601_);
v___x_5742_ = l_Bool_repr___redArg(v_locals_5599_);
v___x_5743_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5664_);
lean_ctor_set(v___x_5743_, 1, v___x_5742_);
v___x_5744_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5744_, 0, v___x_5743_);
lean_ctor_set_uint8(v___x_5744_, sizeof(void*)*1, v___x_5607_);
v___x_5745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5745_, 0, v___x_5741_);
lean_ctor_set(v___x_5745_, 1, v___x_5744_);
v___x_5746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5746_, 0, v___x_5745_);
lean_ctor_set(v___x_5746_, 1, v___x_5610_);
v___x_5747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5747_, 0, v___x_5746_);
lean_ctor_set(v___x_5747_, 1, v___x_5612_);
v___x_5748_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5749_, 0, v___x_5747_);
lean_ctor_set(v___x_5749_, 1, v___x_5748_);
v___x_5750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5750_, 0, v___x_5749_);
lean_ctor_set(v___x_5750_, 1, v___x_5601_);
v___x_5751_ = l_Bool_repr___redArg(v_instances_5600_);
v___x_5752_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5752_, 0, v___x_5636_);
lean_ctor_set(v___x_5752_, 1, v___x_5751_);
v___x_5753_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5753_, 0, v___x_5752_);
lean_ctor_set_uint8(v___x_5753_, sizeof(void*)*1, v___x_5607_);
v___x_5754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5754_, 0, v___x_5750_);
lean_ctor_set(v___x_5754_, 1, v___x_5753_);
v___x_5755_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5756_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5757_, 0, v___x_5756_);
lean_ctor_set(v___x_5757_, 1, v___x_5754_);
v___x_5758_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5759_, 0, v___x_5757_);
lean_ctor_set(v___x_5759_, 1, v___x_5758_);
v___x_5760_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5760_, 0, v___x_5755_);
lean_ctor_set(v___x_5760_, 1, v___x_5759_);
v___x_5761_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5761_, 0, v___x_5760_);
lean_ctor_set_uint8(v___x_5761_, sizeof(void*)*1, v___x_5607_);
return v___x_5761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5762_){
_start:
{
lean_object* v_res_5763_; 
v_res_5763_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5762_);
lean_dec_ref(v_x_5762_);
return v_res_5763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5764_, lean_object* v_prec_5765_){
_start:
{
lean_object* v___x_5766_; 
v___x_5766_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5764_);
return v___x_5766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5767_, lean_object* v_prec_5768_){
_start:
{
lean_object* v_res_5769_; 
v_res_5769_ = l_Lean_Meta_instReprConfig_repr(v_x_5767_, v_prec_5768_);
lean_dec(v_prec_5768_);
lean_dec_ref(v_x_5767_);
return v_res_5769_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5777_, lean_object* v_x_5778_){
_start:
{
if (lean_obj_tag(v_x_5777_) == 0)
{
lean_object* v___x_5779_; 
v___x_5779_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5779_;
}
else
{
lean_object* v_val_5780_; lean_object* v___x_5782_; uint8_t v_isShared_5783_; uint8_t v_isSharedCheck_5791_; 
v_val_5780_ = lean_ctor_get(v_x_5777_, 0);
v_isSharedCheck_5791_ = !lean_is_exclusive(v_x_5777_);
if (v_isSharedCheck_5791_ == 0)
{
v___x_5782_ = v_x_5777_;
v_isShared_5783_ = v_isSharedCheck_5791_;
goto v_resetjp_5781_;
}
else
{
lean_inc(v_val_5780_);
lean_dec(v_x_5777_);
v___x_5782_ = lean_box(0);
v_isShared_5783_ = v_isSharedCheck_5791_;
goto v_resetjp_5781_;
}
v_resetjp_5781_:
{
lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5787_; 
v___x_5784_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5785_ = l_Nat_reprFast(v_val_5780_);
if (v_isShared_5783_ == 0)
{
lean_ctor_set_tag(v___x_5782_, 3);
lean_ctor_set(v___x_5782_, 0, v___x_5785_);
v___x_5787_ = v___x_5782_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5790_; 
v_reuseFailAlloc_5790_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5790_, 0, v___x_5785_);
v___x_5787_ = v_reuseFailAlloc_5790_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
lean_object* v___x_5788_; lean_object* v___x_5789_; 
v___x_5788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5788_, 0, v___x_5784_);
lean_ctor_set(v___x_5788_, 1, v___x_5787_);
v___x_5789_ = l_Repr_addAppParen(v___x_5788_, v_x_5778_);
return v___x_5789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5792_, lean_object* v_x_5793_){
_start:
{
lean_object* v_res_5794_; 
v_res_5794_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5792_, v_x_5793_);
lean_dec(v_x_5793_);
return v_res_5794_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5807_; lean_object* v___x_5808_; 
v___x_5807_ = lean_unsigned_to_nat(21u);
v___x_5808_ = lean_nat_to_int(v___x_5807_);
return v___x_5808_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5815_; lean_object* v___x_5816_; 
v___x_5815_ = lean_unsigned_to_nat(11u);
v___x_5816_ = lean_nat_to_int(v___x_5815_);
return v___x_5816_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5832_; lean_object* v___x_5833_; 
v___x_5832_ = lean_unsigned_to_nat(23u);
v___x_5833_ = lean_nat_to_int(v___x_5832_);
return v___x_5833_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5837_; lean_object* v___x_5838_; 
v___x_5837_ = lean_unsigned_to_nat(16u);
v___x_5838_ = lean_nat_to_int(v___x_5837_);
return v___x_5838_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5845_; lean_object* v___x_5846_; 
v___x_5845_ = lean_unsigned_to_nat(15u);
v___x_5846_ = lean_nat_to_int(v___x_5845_);
return v___x_5846_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5853_ = lean_unsigned_to_nat(17u);
v___x_5854_ = lean_nat_to_int(v___x_5853_);
return v___x_5854_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5861_; lean_object* v___x_5862_; 
v___x_5861_ = lean_unsigned_to_nat(18u);
v___x_5862_ = lean_nat_to_int(v___x_5861_);
return v___x_5862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5863_){
_start:
{
lean_object* v_maxSteps_5864_; lean_object* v_maxDischargeDepth_5865_; uint8_t v_contextual_5866_; uint8_t v_memoize_5867_; uint8_t v_singlePass_5868_; uint8_t v_zeta_5869_; uint8_t v_beta_5870_; uint8_t v_eta_5871_; uint8_t v_etaStruct_5872_; uint8_t v_iota_5873_; uint8_t v_proj_5874_; uint8_t v_decide_5875_; uint8_t v_arith_5876_; uint8_t v_autoUnfold_5877_; uint8_t v_dsimp_5878_; uint8_t v_failIfUnchanged_5879_; uint8_t v_ground_5880_; uint8_t v_unfoldPartialApp_5881_; uint8_t v_zetaDelta_5882_; uint8_t v_index_5883_; uint8_t v_implicitDefEqProofs_5884_; uint8_t v_zetaUnused_5885_; uint8_t v_catchRuntime_5886_; uint8_t v_zetaHave_5887_; uint8_t v_letToHave_5888_; uint8_t v_congrConsts_5889_; uint8_t v_bitVecOfNat_5890_; uint8_t v_warnExponents_5891_; uint8_t v_suggestions_5892_; lean_object* v_maxSuggestions_5893_; uint8_t v_locals_5894_; uint8_t v_instances_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; uint8_t v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; 
v_maxSteps_5864_ = lean_ctor_get(v_x_5863_, 0);
lean_inc(v_maxSteps_5864_);
v_maxDischargeDepth_5865_ = lean_ctor_get(v_x_5863_, 1);
lean_inc(v_maxDischargeDepth_5865_);
v_contextual_5866_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3);
v_memoize_5867_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 1);
v_singlePass_5868_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 2);
v_zeta_5869_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 3);
v_beta_5870_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 4);
v_eta_5871_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 5);
v_etaStruct_5872_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 6);
v_iota_5873_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 7);
v_proj_5874_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 8);
v_decide_5875_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 9);
v_arith_5876_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 10);
v_autoUnfold_5877_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 11);
v_dsimp_5878_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5879_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 13);
v_ground_5880_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5881_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 15);
v_zetaDelta_5882_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 16);
v_index_5883_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5884_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 18);
v_zetaUnused_5885_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 19);
v_catchRuntime_5886_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 20);
v_zetaHave_5887_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 21);
v_letToHave_5888_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 22);
v_congrConsts_5889_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5890_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 24);
v_warnExponents_5891_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 25);
v_suggestions_5892_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 26);
v_maxSuggestions_5893_ = lean_ctor_get(v_x_5863_, 2);
lean_inc(v_maxSuggestions_5893_);
v_locals_5894_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 27);
v_instances_5895_ = lean_ctor_get_uint8(v_x_5863_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5863_);
v___x_5896_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5897_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5898_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5899_ = l_Nat_reprFast(v_maxSteps_5864_);
v___x_5900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5900_, 0, v___x_5899_);
v___x_5901_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5901_, 0, v___x_5898_);
lean_ctor_set(v___x_5901_, 1, v___x_5900_);
v___x_5902_ = 0;
v___x_5903_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5903_, 0, v___x_5901_);
lean_ctor_set_uint8(v___x_5903_, sizeof(void*)*1, v___x_5902_);
v___x_5904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5904_, 0, v___x_5897_);
lean_ctor_set(v___x_5904_, 1, v___x_5903_);
v___x_5905_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5906_, 0, v___x_5904_);
lean_ctor_set(v___x_5906_, 1, v___x_5905_);
v___x_5907_ = lean_box(1);
v___x_5908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5908_, 0, v___x_5906_);
lean_ctor_set(v___x_5908_, 1, v___x_5907_);
v___x_5909_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_5910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5908_);
lean_ctor_set(v___x_5910_, 1, v___x_5909_);
v___x_5911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5911_, 0, v___x_5910_);
lean_ctor_set(v___x_5911_, 1, v___x_5896_);
v___x_5912_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_5913_ = l_Nat_reprFast(v_maxDischargeDepth_5865_);
v___x_5914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5914_, 0, v___x_5913_);
v___x_5915_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5915_, 0, v___x_5912_);
lean_ctor_set(v___x_5915_, 1, v___x_5914_);
v___x_5916_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5916_, 0, v___x_5915_);
lean_ctor_set_uint8(v___x_5916_, sizeof(void*)*1, v___x_5902_);
v___x_5917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5917_, 0, v___x_5911_);
lean_ctor_set(v___x_5917_, 1, v___x_5916_);
v___x_5918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5918_, 0, v___x_5917_);
lean_ctor_set(v___x_5918_, 1, v___x_5905_);
v___x_5919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5919_, 0, v___x_5918_);
lean_ctor_set(v___x_5919_, 1, v___x_5907_);
v___x_5920_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_5921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5921_, 0, v___x_5919_);
lean_ctor_set(v___x_5921_, 1, v___x_5920_);
v___x_5922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5922_, 0, v___x_5921_);
lean_ctor_set(v___x_5922_, 1, v___x_5896_);
v___x_5923_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5924_ = lean_unsigned_to_nat(0u);
v___x_5925_ = l_Bool_repr___redArg(v_contextual_5866_);
v___x_5926_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5926_, 0, v___x_5923_);
lean_ctor_set(v___x_5926_, 1, v___x_5925_);
v___x_5927_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5927_, 0, v___x_5926_);
lean_ctor_set_uint8(v___x_5927_, sizeof(void*)*1, v___x_5902_);
v___x_5928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5928_, 0, v___x_5922_);
lean_ctor_set(v___x_5928_, 1, v___x_5927_);
v___x_5929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5929_, 0, v___x_5928_);
lean_ctor_set(v___x_5929_, 1, v___x_5905_);
v___x_5930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5930_, 0, v___x_5929_);
lean_ctor_set(v___x_5930_, 1, v___x_5907_);
v___x_5931_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_5932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5932_, 0, v___x_5930_);
lean_ctor_set(v___x_5932_, 1, v___x_5931_);
v___x_5933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5933_, 0, v___x_5932_);
lean_ctor_set(v___x_5933_, 1, v___x_5896_);
v___x_5934_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_5935_ = l_Bool_repr___redArg(v_memoize_5867_);
v___x_5936_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5934_);
lean_ctor_set(v___x_5936_, 1, v___x_5935_);
v___x_5937_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5937_, 0, v___x_5936_);
lean_ctor_set_uint8(v___x_5937_, sizeof(void*)*1, v___x_5902_);
v___x_5938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5933_);
lean_ctor_set(v___x_5938_, 1, v___x_5937_);
v___x_5939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5939_, 0, v___x_5938_);
lean_ctor_set(v___x_5939_, 1, v___x_5905_);
v___x_5940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5939_);
lean_ctor_set(v___x_5940_, 1, v___x_5907_);
v___x_5941_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_5942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5940_);
lean_ctor_set(v___x_5942_, 1, v___x_5941_);
v___x_5943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5943_, 0, v___x_5942_);
lean_ctor_set(v___x_5943_, 1, v___x_5896_);
v___x_5944_ = l_Bool_repr___redArg(v_singlePass_5868_);
v___x_5945_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5945_, 0, v___x_5923_);
lean_ctor_set(v___x_5945_, 1, v___x_5944_);
v___x_5946_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5946_, 0, v___x_5945_);
lean_ctor_set_uint8(v___x_5946_, sizeof(void*)*1, v___x_5902_);
v___x_5947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5947_, 0, v___x_5943_);
lean_ctor_set(v___x_5947_, 1, v___x_5946_);
v___x_5948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5948_, 0, v___x_5947_);
lean_ctor_set(v___x_5948_, 1, v___x_5905_);
v___x_5949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5948_);
lean_ctor_set(v___x_5949_, 1, v___x_5907_);
v___x_5950_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_5951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5951_, 0, v___x_5949_);
lean_ctor_set(v___x_5951_, 1, v___x_5950_);
v___x_5952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5952_, 0, v___x_5951_);
lean_ctor_set(v___x_5952_, 1, v___x_5896_);
v___x_5953_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5954_ = l_Bool_repr___redArg(v_zeta_5869_);
v___x_5955_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5955_, 0, v___x_5953_);
lean_ctor_set(v___x_5955_, 1, v___x_5954_);
v___x_5956_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5956_, 0, v___x_5955_);
lean_ctor_set_uint8(v___x_5956_, sizeof(void*)*1, v___x_5902_);
v___x_5957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5952_);
lean_ctor_set(v___x_5957_, 1, v___x_5956_);
v___x_5958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5958_, 0, v___x_5957_);
lean_ctor_set(v___x_5958_, 1, v___x_5905_);
v___x_5959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5958_);
lean_ctor_set(v___x_5959_, 1, v___x_5907_);
v___x_5960_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5961_, 0, v___x_5959_);
lean_ctor_set(v___x_5961_, 1, v___x_5960_);
v___x_5962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5962_, 0, v___x_5961_);
lean_ctor_set(v___x_5962_, 1, v___x_5896_);
v___x_5963_ = l_Bool_repr___redArg(v_beta_5870_);
v___x_5964_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5964_, 0, v___x_5953_);
lean_ctor_set(v___x_5964_, 1, v___x_5963_);
v___x_5965_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5965_, 0, v___x_5964_);
lean_ctor_set_uint8(v___x_5965_, sizeof(void*)*1, v___x_5902_);
v___x_5966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5966_, 0, v___x_5962_);
lean_ctor_set(v___x_5966_, 1, v___x_5965_);
v___x_5967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5967_, 0, v___x_5966_);
lean_ctor_set(v___x_5967_, 1, v___x_5905_);
v___x_5968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5967_);
lean_ctor_set(v___x_5968_, 1, v___x_5907_);
v___x_5969_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5970_, 0, v___x_5968_);
lean_ctor_set(v___x_5970_, 1, v___x_5969_);
v___x_5971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5971_, 0, v___x_5970_);
lean_ctor_set(v___x_5971_, 1, v___x_5896_);
v___x_5972_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5973_ = l_Bool_repr___redArg(v_eta_5871_);
v___x_5974_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5972_);
lean_ctor_set(v___x_5974_, 1, v___x_5973_);
v___x_5975_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5975_, 0, v___x_5974_);
lean_ctor_set_uint8(v___x_5975_, sizeof(void*)*1, v___x_5902_);
v___x_5976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5971_);
lean_ctor_set(v___x_5976_, 1, v___x_5975_);
v___x_5977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5977_, 0, v___x_5976_);
lean_ctor_set(v___x_5977_, 1, v___x_5905_);
v___x_5978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5977_);
lean_ctor_set(v___x_5978_, 1, v___x_5907_);
v___x_5979_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5980_, 0, v___x_5978_);
lean_ctor_set(v___x_5980_, 1, v___x_5979_);
v___x_5981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5981_, 0, v___x_5980_);
lean_ctor_set(v___x_5981_, 1, v___x_5896_);
v___x_5982_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5983_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5872_, v___x_5924_);
v___x_5984_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5984_, 0, v___x_5982_);
lean_ctor_set(v___x_5984_, 1, v___x_5983_);
v___x_5985_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5985_, 0, v___x_5984_);
lean_ctor_set_uint8(v___x_5985_, sizeof(void*)*1, v___x_5902_);
v___x_5986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5986_, 0, v___x_5981_);
lean_ctor_set(v___x_5986_, 1, v___x_5985_);
v___x_5987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5987_, 0, v___x_5986_);
lean_ctor_set(v___x_5987_, 1, v___x_5905_);
v___x_5988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5988_, 0, v___x_5987_);
lean_ctor_set(v___x_5988_, 1, v___x_5907_);
v___x_5989_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5990_, 0, v___x_5988_);
lean_ctor_set(v___x_5990_, 1, v___x_5989_);
v___x_5991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5990_);
lean_ctor_set(v___x_5991_, 1, v___x_5896_);
v___x_5992_ = l_Bool_repr___redArg(v_iota_5873_);
v___x_5993_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5953_);
lean_ctor_set(v___x_5993_, 1, v___x_5992_);
v___x_5994_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5994_, 0, v___x_5993_);
lean_ctor_set_uint8(v___x_5994_, sizeof(void*)*1, v___x_5902_);
v___x_5995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5995_, 0, v___x_5991_);
lean_ctor_set(v___x_5995_, 1, v___x_5994_);
v___x_5996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5995_);
lean_ctor_set(v___x_5996_, 1, v___x_5905_);
v___x_5997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5997_, 0, v___x_5996_);
lean_ctor_set(v___x_5997_, 1, v___x_5907_);
v___x_5998_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5999_, 0, v___x_5997_);
lean_ctor_set(v___x_5999_, 1, v___x_5998_);
v___x_6000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6000_, 0, v___x_5999_);
lean_ctor_set(v___x_6000_, 1, v___x_5896_);
v___x_6001_ = l_Bool_repr___redArg(v_proj_5874_);
v___x_6002_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6002_, 0, v___x_5953_);
lean_ctor_set(v___x_6002_, 1, v___x_6001_);
v___x_6003_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6003_, 0, v___x_6002_);
lean_ctor_set_uint8(v___x_6003_, sizeof(void*)*1, v___x_5902_);
v___x_6004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6004_, 0, v___x_6000_);
lean_ctor_set(v___x_6004_, 1, v___x_6003_);
v___x_6005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6005_, 0, v___x_6004_);
lean_ctor_set(v___x_6005_, 1, v___x_5905_);
v___x_6006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6005_);
lean_ctor_set(v___x_6006_, 1, v___x_5907_);
v___x_6007_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_6008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6008_, 0, v___x_6006_);
lean_ctor_set(v___x_6008_, 1, v___x_6007_);
v___x_6009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6009_, 0, v___x_6008_);
lean_ctor_set(v___x_6009_, 1, v___x_5896_);
v___x_6010_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_6011_ = l_Bool_repr___redArg(v_decide_5875_);
v___x_6012_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6012_, 0, v___x_6010_);
lean_ctor_set(v___x_6012_, 1, v___x_6011_);
v___x_6013_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6013_, 0, v___x_6012_);
lean_ctor_set_uint8(v___x_6013_, sizeof(void*)*1, v___x_5902_);
v___x_6014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6009_);
lean_ctor_set(v___x_6014_, 1, v___x_6013_);
v___x_6015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6014_);
lean_ctor_set(v___x_6015_, 1, v___x_5905_);
v___x_6016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6015_);
lean_ctor_set(v___x_6016_, 1, v___x_5907_);
v___x_6017_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_6018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6018_, 0, v___x_6016_);
lean_ctor_set(v___x_6018_, 1, v___x_6017_);
v___x_6019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6019_, 0, v___x_6018_);
lean_ctor_set(v___x_6019_, 1, v___x_5896_);
v___x_6020_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_6021_ = l_Bool_repr___redArg(v_arith_5876_);
v___x_6022_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6020_);
lean_ctor_set(v___x_6022_, 1, v___x_6021_);
v___x_6023_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6023_, 0, v___x_6022_);
lean_ctor_set_uint8(v___x_6023_, sizeof(void*)*1, v___x_5902_);
v___x_6024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6024_, 0, v___x_6019_);
lean_ctor_set(v___x_6024_, 1, v___x_6023_);
v___x_6025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6025_, 0, v___x_6024_);
lean_ctor_set(v___x_6025_, 1, v___x_5905_);
v___x_6026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6025_);
lean_ctor_set(v___x_6026_, 1, v___x_5907_);
v___x_6027_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_6028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6028_, 0, v___x_6026_);
lean_ctor_set(v___x_6028_, 1, v___x_6027_);
v___x_6029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6029_, 0, v___x_6028_);
lean_ctor_set(v___x_6029_, 1, v___x_5896_);
v___x_6030_ = l_Bool_repr___redArg(v_autoUnfold_5877_);
v___x_6031_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_5923_);
lean_ctor_set(v___x_6031_, 1, v___x_6030_);
v___x_6032_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6032_, 0, v___x_6031_);
lean_ctor_set_uint8(v___x_6032_, sizeof(void*)*1, v___x_5902_);
v___x_6033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6033_, 0, v___x_6029_);
lean_ctor_set(v___x_6033_, 1, v___x_6032_);
v___x_6034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6033_);
lean_ctor_set(v___x_6034_, 1, v___x_5905_);
v___x_6035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6034_);
lean_ctor_set(v___x_6035_, 1, v___x_5907_);
v___x_6036_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_6037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6037_, 0, v___x_6035_);
lean_ctor_set(v___x_6037_, 1, v___x_6036_);
v___x_6038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6038_, 0, v___x_6037_);
lean_ctor_set(v___x_6038_, 1, v___x_5896_);
v___x_6039_ = l_Bool_repr___redArg(v_dsimp_5878_);
v___x_6040_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6020_);
lean_ctor_set(v___x_6040_, 1, v___x_6039_);
v___x_6041_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6041_, 0, v___x_6040_);
lean_ctor_set_uint8(v___x_6041_, sizeof(void*)*1, v___x_5902_);
v___x_6042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6042_, 0, v___x_6038_);
lean_ctor_set(v___x_6042_, 1, v___x_6041_);
v___x_6043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6043_, 0, v___x_6042_);
lean_ctor_set(v___x_6043_, 1, v___x_5905_);
v___x_6044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6044_, 0, v___x_6043_);
lean_ctor_set(v___x_6044_, 1, v___x_5907_);
v___x_6045_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_6046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6046_, 0, v___x_6044_);
lean_ctor_set(v___x_6046_, 1, v___x_6045_);
v___x_6047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6047_, 0, v___x_6046_);
lean_ctor_set(v___x_6047_, 1, v___x_5896_);
v___x_6048_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_6049_ = l_Bool_repr___redArg(v_failIfUnchanged_5879_);
v___x_6050_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6048_);
lean_ctor_set(v___x_6050_, 1, v___x_6049_);
v___x_6051_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6051_, 0, v___x_6050_);
lean_ctor_set_uint8(v___x_6051_, sizeof(void*)*1, v___x_5902_);
v___x_6052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6052_, 0, v___x_6047_);
lean_ctor_set(v___x_6052_, 1, v___x_6051_);
v___x_6053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6053_, 0, v___x_6052_);
lean_ctor_set(v___x_6053_, 1, v___x_5905_);
v___x_6054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6053_);
lean_ctor_set(v___x_6054_, 1, v___x_5907_);
v___x_6055_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_6056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6056_, 0, v___x_6054_);
lean_ctor_set(v___x_6056_, 1, v___x_6055_);
v___x_6057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6057_, 0, v___x_6056_);
lean_ctor_set(v___x_6057_, 1, v___x_5896_);
v___x_6058_ = l_Bool_repr___redArg(v_ground_5880_);
v___x_6059_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6059_, 0, v___x_6010_);
lean_ctor_set(v___x_6059_, 1, v___x_6058_);
v___x_6060_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6060_, 0, v___x_6059_);
lean_ctor_set_uint8(v___x_6060_, sizeof(void*)*1, v___x_5902_);
v___x_6061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6057_);
lean_ctor_set(v___x_6061_, 1, v___x_6060_);
v___x_6062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6062_, 0, v___x_6061_);
lean_ctor_set(v___x_6062_, 1, v___x_5905_);
v___x_6063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6063_, 0, v___x_6062_);
lean_ctor_set(v___x_6063_, 1, v___x_5907_);
v___x_6064_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_6065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6063_);
lean_ctor_set(v___x_6065_, 1, v___x_6064_);
v___x_6066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6065_);
lean_ctor_set(v___x_6066_, 1, v___x_5896_);
v___x_6067_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_6068_ = l_Bool_repr___redArg(v_unfoldPartialApp_5881_);
v___x_6069_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6067_);
lean_ctor_set(v___x_6069_, 1, v___x_6068_);
v___x_6070_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6070_, 0, v___x_6069_);
lean_ctor_set_uint8(v___x_6070_, sizeof(void*)*1, v___x_5902_);
v___x_6071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6066_);
lean_ctor_set(v___x_6071_, 1, v___x_6070_);
v___x_6072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6071_);
lean_ctor_set(v___x_6072_, 1, v___x_5905_);
v___x_6073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6072_);
lean_ctor_set(v___x_6073_, 1, v___x_5907_);
v___x_6074_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6075_, 0, v___x_6073_);
lean_ctor_set(v___x_6075_, 1, v___x_6074_);
v___x_6076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6076_, 0, v___x_6075_);
lean_ctor_set(v___x_6076_, 1, v___x_5896_);
v___x_6077_ = l_Bool_repr___redArg(v_zetaDelta_5882_);
v___x_6078_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_5982_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6079_, 0, v___x_6078_);
lean_ctor_set_uint8(v___x_6079_, sizeof(void*)*1, v___x_5902_);
v___x_6080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6080_, 0, v___x_6076_);
lean_ctor_set(v___x_6080_, 1, v___x_6079_);
v___x_6081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6081_, 0, v___x_6080_);
lean_ctor_set(v___x_6081_, 1, v___x_5905_);
v___x_6082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6081_);
lean_ctor_set(v___x_6082_, 1, v___x_5907_);
v___x_6083_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6084_, 0, v___x_6082_);
lean_ctor_set(v___x_6084_, 1, v___x_6083_);
v___x_6085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6085_, 0, v___x_6084_);
lean_ctor_set(v___x_6085_, 1, v___x_5896_);
v___x_6086_ = l_Bool_repr___redArg(v_index_5883_);
v___x_6087_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6087_, 0, v___x_6020_);
lean_ctor_set(v___x_6087_, 1, v___x_6086_);
v___x_6088_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6088_, 0, v___x_6087_);
lean_ctor_set_uint8(v___x_6088_, sizeof(void*)*1, v___x_5902_);
v___x_6089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6085_);
lean_ctor_set(v___x_6089_, 1, v___x_6088_);
v___x_6090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6090_, 0, v___x_6089_);
lean_ctor_set(v___x_6090_, 1, v___x_5905_);
v___x_6091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6090_);
lean_ctor_set(v___x_6091_, 1, v___x_5907_);
v___x_6092_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6091_);
lean_ctor_set(v___x_6093_, 1, v___x_6092_);
v___x_6094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___x_6093_);
lean_ctor_set(v___x_6094_, 1, v___x_5896_);
v___x_6095_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6096_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5884_);
v___x_6097_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6097_, 0, v___x_6095_);
lean_ctor_set(v___x_6097_, 1, v___x_6096_);
v___x_6098_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6098_, 0, v___x_6097_);
lean_ctor_set_uint8(v___x_6098_, sizeof(void*)*1, v___x_5902_);
v___x_6099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6099_, 0, v___x_6094_);
lean_ctor_set(v___x_6099_, 1, v___x_6098_);
v___x_6100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6099_);
lean_ctor_set(v___x_6100_, 1, v___x_5905_);
v___x_6101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6100_);
lean_ctor_set(v___x_6101_, 1, v___x_5907_);
v___x_6102_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6101_);
lean_ctor_set(v___x_6103_, 1, v___x_6102_);
v___x_6104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
lean_ctor_set(v___x_6104_, 1, v___x_5896_);
v___x_6105_ = l_Bool_repr___redArg(v_zetaUnused_5885_);
v___x_6106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6106_, 0, v___x_5923_);
lean_ctor_set(v___x_6106_, 1, v___x_6105_);
v___x_6107_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6107_, 0, v___x_6106_);
lean_ctor_set_uint8(v___x_6107_, sizeof(void*)*1, v___x_5902_);
v___x_6108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6108_, 0, v___x_6104_);
lean_ctor_set(v___x_6108_, 1, v___x_6107_);
v___x_6109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6109_, 0, v___x_6108_);
lean_ctor_set(v___x_6109_, 1, v___x_5905_);
v___x_6110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6110_, 0, v___x_6109_);
lean_ctor_set(v___x_6110_, 1, v___x_5907_);
v___x_6111_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6112_, 0, v___x_6110_);
lean_ctor_set(v___x_6112_, 1, v___x_6111_);
v___x_6113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6112_);
lean_ctor_set(v___x_6113_, 1, v___x_5896_);
v___x_6114_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6115_ = l_Bool_repr___redArg(v_catchRuntime_5886_);
v___x_6116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6114_);
lean_ctor_set(v___x_6116_, 1, v___x_6115_);
v___x_6117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6117_, 0, v___x_6116_);
lean_ctor_set_uint8(v___x_6117_, sizeof(void*)*1, v___x_5902_);
v___x_6118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6113_);
lean_ctor_set(v___x_6118_, 1, v___x_6117_);
v___x_6119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6119_, 0, v___x_6118_);
lean_ctor_set(v___x_6119_, 1, v___x_5905_);
v___x_6120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6119_);
lean_ctor_set(v___x_6120_, 1, v___x_5907_);
v___x_6121_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6122_, 0, v___x_6120_);
lean_ctor_set(v___x_6122_, 1, v___x_6121_);
v___x_6123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6123_, 0, v___x_6122_);
lean_ctor_set(v___x_6123_, 1, v___x_5896_);
v___x_6124_ = l_Bool_repr___redArg(v_zetaHave_5887_);
v___x_6125_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6125_, 0, v___x_5898_);
lean_ctor_set(v___x_6125_, 1, v___x_6124_);
v___x_6126_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6126_, 0, v___x_6125_);
lean_ctor_set_uint8(v___x_6126_, sizeof(void*)*1, v___x_5902_);
v___x_6127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6127_, 0, v___x_6123_);
lean_ctor_set(v___x_6127_, 1, v___x_6126_);
v___x_6128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6128_, 0, v___x_6127_);
lean_ctor_set(v___x_6128_, 1, v___x_5905_);
v___x_6129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6128_);
lean_ctor_set(v___x_6129_, 1, v___x_5907_);
v___x_6130_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6131_, 0, v___x_6129_);
lean_ctor_set(v___x_6131_, 1, v___x_6130_);
v___x_6132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6131_);
lean_ctor_set(v___x_6132_, 1, v___x_5896_);
v___x_6133_ = l_Bool_repr___redArg(v_letToHave_5888_);
v___x_6134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6134_, 0, v___x_5982_);
lean_ctor_set(v___x_6134_, 1, v___x_6133_);
v___x_6135_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6135_, 0, v___x_6134_);
lean_ctor_set_uint8(v___x_6135_, sizeof(void*)*1, v___x_5902_);
v___x_6136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6136_, 0, v___x_6132_);
lean_ctor_set(v___x_6136_, 1, v___x_6135_);
v___x_6137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6137_, 0, v___x_6136_);
lean_ctor_set(v___x_6137_, 1, v___x_5905_);
v___x_6138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6138_, 0, v___x_6137_);
lean_ctor_set(v___x_6138_, 1, v___x_5907_);
v___x_6139_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6140_, 0, v___x_6138_);
lean_ctor_set(v___x_6140_, 1, v___x_6139_);
v___x_6141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6141_, 0, v___x_6140_);
lean_ctor_set(v___x_6141_, 1, v___x_5896_);
v___x_6142_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6143_ = l_Bool_repr___redArg(v_congrConsts_5889_);
v___x_6144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6142_);
lean_ctor_set(v___x_6144_, 1, v___x_6143_);
v___x_6145_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6145_, 0, v___x_6144_);
lean_ctor_set_uint8(v___x_6145_, sizeof(void*)*1, v___x_5902_);
v___x_6146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6146_, 0, v___x_6141_);
lean_ctor_set(v___x_6146_, 1, v___x_6145_);
v___x_6147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6147_, 0, v___x_6146_);
lean_ctor_set(v___x_6147_, 1, v___x_5905_);
v___x_6148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6147_);
lean_ctor_set(v___x_6148_, 1, v___x_5907_);
v___x_6149_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6150_, 0, v___x_6148_);
lean_ctor_set(v___x_6150_, 1, v___x_6149_);
v___x_6151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6151_, 0, v___x_6150_);
lean_ctor_set(v___x_6151_, 1, v___x_5896_);
v___x_6152_ = l_Bool_repr___redArg(v_bitVecOfNat_5890_);
v___x_6153_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6153_, 0, v___x_6142_);
lean_ctor_set(v___x_6153_, 1, v___x_6152_);
v___x_6154_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6154_, 0, v___x_6153_);
lean_ctor_set_uint8(v___x_6154_, sizeof(void*)*1, v___x_5902_);
v___x_6155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6155_, 0, v___x_6151_);
lean_ctor_set(v___x_6155_, 1, v___x_6154_);
v___x_6156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6156_, 0, v___x_6155_);
lean_ctor_set(v___x_6156_, 1, v___x_5905_);
v___x_6157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6157_, 0, v___x_6156_);
lean_ctor_set(v___x_6157_, 1, v___x_5907_);
v___x_6158_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6157_);
lean_ctor_set(v___x_6159_, 1, v___x_6158_);
v___x_6160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6160_, 0, v___x_6159_);
lean_ctor_set(v___x_6160_, 1, v___x_5896_);
v___x_6161_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6162_ = l_Bool_repr___redArg(v_warnExponents_5891_);
v___x_6163_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6163_, 0, v___x_6161_);
lean_ctor_set(v___x_6163_, 1, v___x_6162_);
v___x_6164_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6164_, 0, v___x_6163_);
lean_ctor_set_uint8(v___x_6164_, sizeof(void*)*1, v___x_5902_);
v___x_6165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6165_, 0, v___x_6160_);
lean_ctor_set(v___x_6165_, 1, v___x_6164_);
v___x_6166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6166_, 0, v___x_6165_);
lean_ctor_set(v___x_6166_, 1, v___x_5905_);
v___x_6167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6167_, 0, v___x_6166_);
lean_ctor_set(v___x_6167_, 1, v___x_5907_);
v___x_6168_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6169_, 0, v___x_6167_);
lean_ctor_set(v___x_6169_, 1, v___x_6168_);
v___x_6170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6170_, 0, v___x_6169_);
lean_ctor_set(v___x_6170_, 1, v___x_5896_);
v___x_6171_ = l_Bool_repr___redArg(v_suggestions_5892_);
v___x_6172_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6172_, 0, v___x_6142_);
lean_ctor_set(v___x_6172_, 1, v___x_6171_);
v___x_6173_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6173_, 0, v___x_6172_);
lean_ctor_set_uint8(v___x_6173_, sizeof(void*)*1, v___x_5902_);
v___x_6174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6174_, 0, v___x_6170_);
lean_ctor_set(v___x_6174_, 1, v___x_6173_);
v___x_6175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6175_, 0, v___x_6174_);
lean_ctor_set(v___x_6175_, 1, v___x_5905_);
v___x_6176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6175_);
lean_ctor_set(v___x_6176_, 1, v___x_5907_);
v___x_6177_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6178_, 0, v___x_6176_);
lean_ctor_set(v___x_6178_, 1, v___x_6177_);
v___x_6179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6178_);
lean_ctor_set(v___x_6179_, 1, v___x_5896_);
v___x_6180_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6181_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5893_, v___x_5924_);
v___x_6182_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6182_, 0, v___x_6180_);
lean_ctor_set(v___x_6182_, 1, v___x_6181_);
v___x_6183_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6183_, 0, v___x_6182_);
lean_ctor_set_uint8(v___x_6183_, sizeof(void*)*1, v___x_5902_);
v___x_6184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6184_, 0, v___x_6179_);
lean_ctor_set(v___x_6184_, 1, v___x_6183_);
v___x_6185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6185_, 0, v___x_6184_);
lean_ctor_set(v___x_6185_, 1, v___x_5905_);
v___x_6186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6186_, 0, v___x_6185_);
lean_ctor_set(v___x_6186_, 1, v___x_5907_);
v___x_6187_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6188_, 0, v___x_6186_);
lean_ctor_set(v___x_6188_, 1, v___x_6187_);
v___x_6189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6189_, 0, v___x_6188_);
lean_ctor_set(v___x_6189_, 1, v___x_5896_);
v___x_6190_ = l_Bool_repr___redArg(v_locals_5894_);
v___x_6191_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6191_, 0, v___x_6010_);
lean_ctor_set(v___x_6191_, 1, v___x_6190_);
v___x_6192_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6192_, 0, v___x_6191_);
lean_ctor_set_uint8(v___x_6192_, sizeof(void*)*1, v___x_5902_);
v___x_6193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6193_, 0, v___x_6189_);
lean_ctor_set(v___x_6193_, 1, v___x_6192_);
v___x_6194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6194_, 0, v___x_6193_);
lean_ctor_set(v___x_6194_, 1, v___x_5905_);
v___x_6195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6195_, 0, v___x_6194_);
lean_ctor_set(v___x_6195_, 1, v___x_5907_);
v___x_6196_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6197_, 0, v___x_6195_);
lean_ctor_set(v___x_6197_, 1, v___x_6196_);
v___x_6198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6198_, 0, v___x_6197_);
lean_ctor_set(v___x_6198_, 1, v___x_5896_);
v___x_6199_ = l_Bool_repr___redArg(v_instances_5895_);
v___x_6200_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6200_, 0, v___x_5982_);
lean_ctor_set(v___x_6200_, 1, v___x_6199_);
v___x_6201_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6201_, 0, v___x_6200_);
lean_ctor_set_uint8(v___x_6201_, sizeof(void*)*1, v___x_5902_);
v___x_6202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6202_, 0, v___x_6198_);
lean_ctor_set(v___x_6202_, 1, v___x_6201_);
v___x_6203_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6204_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6205_, 0, v___x_6204_);
lean_ctor_set(v___x_6205_, 1, v___x_6202_);
v___x_6206_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6207_, 0, v___x_6205_);
lean_ctor_set(v___x_6207_, 1, v___x_6206_);
v___x_6208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6208_, 0, v___x_6203_);
lean_ctor_set(v___x_6208_, 1, v___x_6207_);
v___x_6209_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6209_, 0, v___x_6208_);
lean_ctor_set_uint8(v___x_6209_, sizeof(void*)*1, v___x_5902_);
return v___x_6209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6210_, lean_object* v_prec_6211_){
_start:
{
lean_object* v___x_6212_; 
v___x_6212_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6210_);
return v___x_6212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6213_, lean_object* v_prec_6214_){
_start:
{
lean_object* v_res_6215_; 
v_res_6215_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6213_, v_prec_6214_);
lean_dec(v_prec_6214_);
return v_res_6215_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6218_, lean_object* v_x_6219_){
_start:
{
if (lean_obj_tag(v_x_6219_) == 0)
{
uint8_t v___x_6220_; 
v___x_6220_ = 0;
return v___x_6220_;
}
else
{
lean_object* v_head_6221_; lean_object* v_tail_6222_; uint8_t v___x_6223_; 
v_head_6221_ = lean_ctor_get(v_x_6219_, 0);
v_tail_6222_ = lean_ctor_get(v_x_6219_, 1);
v___x_6223_ = lean_nat_dec_eq(v_a_6218_, v_head_6221_);
if (v___x_6223_ == 0)
{
v_x_6219_ = v_tail_6222_;
goto _start;
}
else
{
return v___x_6223_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6225_, lean_object* v_x_6226_){
_start:
{
uint8_t v_res_6227_; lean_object* v_r_6228_; 
v_res_6227_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6225_, v_x_6226_);
lean_dec(v_x_6226_);
lean_dec(v_a_6225_);
v_r_6228_ = lean_box(v_res_6227_);
return v_r_6228_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6229_, lean_object* v_x_6230_){
_start:
{
switch(lean_obj_tag(v_x_6229_))
{
case 0:
{
uint8_t v___x_6231_; 
v___x_6231_ = 1;
return v___x_6231_;
}
case 1:
{
lean_object* v_idxs_6232_; uint8_t v___x_6233_; 
v_idxs_6232_ = lean_ctor_get(v_x_6229_, 0);
v___x_6233_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6230_, v_idxs_6232_);
return v___x_6233_;
}
default: 
{
lean_object* v_idxs_6234_; uint8_t v___x_6235_; uint8_t v___x_6236_; 
v_idxs_6234_ = lean_ctor_get(v_x_6229_, 0);
v___x_6235_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6230_, v_idxs_6234_);
v___x_6236_ = lean_bool_not(v___x_6235_);
return v___x_6236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6237_, lean_object* v_x_6238_){
_start:
{
uint8_t v_res_6239_; lean_object* v_r_6240_; 
v_res_6239_ = l_Lean_Meta_Occurrences_contains(v_x_6237_, v_x_6238_);
lean_dec(v_x_6238_);
lean_dec(v_x_6237_);
v_r_6240_ = lean_box(v_res_6239_);
return v_r_6240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6241_){
_start:
{
if (lean_obj_tag(v_x_6241_) == 0)
{
uint8_t v___x_6242_; 
v___x_6242_ = 1;
return v___x_6242_;
}
else
{
uint8_t v___x_6243_; 
v___x_6243_ = 0;
return v___x_6243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6244_){
_start:
{
uint8_t v_res_6245_; lean_object* v_r_6246_; 
v_res_6245_ = l_Lean_Meta_Occurrences_isAll(v_x_6244_);
lean_dec(v_x_6244_);
v_r_6246_ = lean_box(v_res_6245_);
return v_r_6246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t v_x_6247_){
_start:
{
switch(v_x_6247_)
{
case 0:
{
lean_object* v___x_6248_; 
v___x_6248_ = lean_unsigned_to_nat(0u);
return v___x_6248_;
}
case 1:
{
lean_object* v___x_6249_; 
v___x_6249_ = lean_unsigned_to_nat(1u);
return v___x_6249_;
}
default: 
{
lean_object* v___x_6250_; 
v___x_6250_ = lean_unsigned_to_nat(2u);
return v___x_6250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object* v_x_6251_){
_start:
{
uint8_t v_x_boxed_6252_; lean_object* v_res_6253_; 
v_x_boxed_6252_ = lean_unbox(v_x_6251_);
v_res_6253_ = l_Lean_Meta_ApplyNewGoals_ctorIdx(v_x_boxed_6252_);
return v_res_6253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx(uint8_t v_x_6254_){
_start:
{
lean_object* v___x_6255_; 
v___x_6255_ = l_Lean_Meta_ApplyNewGoals_ctorIdx(v_x_6254_);
return v___x_6255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx___boxed(lean_object* v_x_6256_){
_start:
{
uint8_t v_x_4__boxed_6257_; lean_object* v_res_6258_; 
v_x_4__boxed_6257_ = lean_unbox(v_x_6256_);
v_res_6258_ = l_Lean_Meta_ApplyNewGoals_toCtorIdx(v_x_4__boxed_6257_);
return v_res_6258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6259_){
_start:
{
lean_inc(v_k_6259_);
return v_k_6259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6260_){
_start:
{
lean_object* v_res_6261_; 
v_res_6261_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6260_);
lean_dec(v_k_6260_);
return v_res_6261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6262_, lean_object* v_ctorIdx_6263_, uint8_t v_t_6264_, lean_object* v_h_6265_, lean_object* v_k_6266_){
_start:
{
lean_inc(v_k_6266_);
return v_k_6266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6267_, lean_object* v_ctorIdx_6268_, lean_object* v_t_6269_, lean_object* v_h_6270_, lean_object* v_k_6271_){
_start:
{
uint8_t v_t_boxed_6272_; lean_object* v_res_6273_; 
v_t_boxed_6272_ = lean_unbox(v_t_6269_);
v_res_6273_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6267_, v_ctorIdx_6268_, v_t_boxed_6272_, v_h_6270_, v_k_6271_);
lean_dec(v_k_6271_);
lean_dec(v_ctorIdx_6268_);
return v_res_6273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6274_){
_start:
{
lean_inc(v_nonDependentFirst_6274_);
return v_nonDependentFirst_6274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6275_){
_start:
{
lean_object* v_res_6276_; 
v_res_6276_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6275_);
lean_dec(v_nonDependentFirst_6275_);
return v_res_6276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6277_, uint8_t v_t_6278_, lean_object* v_h_6279_, lean_object* v_nonDependentFirst_6280_){
_start:
{
lean_inc(v_nonDependentFirst_6280_);
return v_nonDependentFirst_6280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6281_, lean_object* v_t_6282_, lean_object* v_h_6283_, lean_object* v_nonDependentFirst_6284_){
_start:
{
uint8_t v_t_boxed_6285_; lean_object* v_res_6286_; 
v_t_boxed_6285_ = lean_unbox(v_t_6282_);
v_res_6286_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6281_, v_t_boxed_6285_, v_h_6283_, v_nonDependentFirst_6284_);
lean_dec(v_nonDependentFirst_6284_);
return v_res_6286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6287_){
_start:
{
lean_inc(v_nonDependentOnly_6287_);
return v_nonDependentOnly_6287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6288_){
_start:
{
lean_object* v_res_6289_; 
v_res_6289_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6288_);
lean_dec(v_nonDependentOnly_6288_);
return v_res_6289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6290_, uint8_t v_t_6291_, lean_object* v_h_6292_, lean_object* v_nonDependentOnly_6293_){
_start:
{
lean_inc(v_nonDependentOnly_6293_);
return v_nonDependentOnly_6293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6294_, lean_object* v_t_6295_, lean_object* v_h_6296_, lean_object* v_nonDependentOnly_6297_){
_start:
{
uint8_t v_t_boxed_6298_; lean_object* v_res_6299_; 
v_t_boxed_6298_ = lean_unbox(v_t_6295_);
v_res_6299_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6294_, v_t_boxed_6298_, v_h_6296_, v_nonDependentOnly_6297_);
lean_dec(v_nonDependentOnly_6297_);
return v_res_6299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6300_){
_start:
{
lean_inc(v_all_6300_);
return v_all_6300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6301_){
_start:
{
lean_object* v_res_6302_; 
v_res_6302_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6301_);
lean_dec(v_all_6301_);
return v_res_6302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6303_, uint8_t v_t_6304_, lean_object* v_h_6305_, lean_object* v_all_6306_){
_start:
{
lean_inc(v_all_6306_);
return v_all_6306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6307_, lean_object* v_t_6308_, lean_object* v_h_6309_, lean_object* v_all_6310_){
_start:
{
uint8_t v_t_boxed_6311_; lean_object* v_res_6312_; 
v_t_boxed_6311_ = lean_unbox(v_t_6308_);
v_res_6312_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6307_, v_t_boxed_6311_, v_h_6309_, v_all_6310_);
lean_dec(v_all_6310_);
return v_res_6312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6326_){
_start:
{
lean_object* v___x_6327_; uint8_t v___x_6328_; 
v___x_6327_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6326_);
v___x_6328_ = l_Lean_Syntax_isOfKind(v_c_6326_, v___x_6327_);
if (v___x_6328_ == 0)
{
lean_object* v___x_6329_; uint8_t v___x_6330_; 
v___x_6329_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6326_);
v___x_6330_ = l_Lean_Syntax_isOfKind(v_c_6326_, v___x_6329_);
if (v___x_6330_ == 0)
{
lean_object* v___x_6331_; uint8_t v___x_6332_; 
v___x_6331_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6326_);
v___x_6332_ = l_Lean_Syntax_isOfKind(v_c_6326_, v___x_6331_);
if (v___x_6332_ == 0)
{
lean_object* v___x_6333_; 
lean_dec(v_c_6326_);
v___x_6333_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6333_;
}
else
{
lean_object* v___x_6334_; lean_object* v___x_6335_; lean_object* v___x_6336_; 
v___x_6334_ = lean_unsigned_to_nat(1u);
v___x_6335_ = lean_mk_empty_array_with_capacity(v___x_6334_);
v___x_6336_ = lean_array_push(v___x_6335_, v_c_6326_);
return v___x_6336_;
}
}
else
{
lean_object* v___x_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; 
v___x_6337_ = lean_unsigned_to_nat(0u);
v___x_6338_ = l_Lean_Syntax_getArg(v_c_6326_, v___x_6337_);
lean_dec(v_c_6326_);
v___x_6339_ = l_Lean_Syntax_getArgs(v___x_6338_);
lean_dec(v___x_6338_);
return v___x_6339_;
}
}
else
{
lean_object* v___x_6340_; lean_object* v___x_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; uint8_t v___x_6344_; 
v___x_6340_ = l_Lean_Syntax_getArgs(v_c_6326_);
lean_dec(v_c_6326_);
v___x_6341_ = lean_unsigned_to_nat(0u);
v___x_6342_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6343_ = lean_array_get_size(v___x_6340_);
v___x_6344_ = lean_nat_dec_lt(v___x_6341_, v___x_6343_);
if (v___x_6344_ == 0)
{
lean_dec_ref(v___x_6340_);
return v___x_6342_;
}
else
{
uint8_t v___x_6345_; 
v___x_6345_ = lean_nat_dec_le(v___x_6343_, v___x_6343_);
if (v___x_6345_ == 0)
{
if (v___x_6344_ == 0)
{
lean_dec_ref(v___x_6340_);
return v___x_6342_;
}
else
{
size_t v___x_6346_; size_t v___x_6347_; lean_object* v___x_6348_; 
v___x_6346_ = ((size_t)0ULL);
v___x_6347_ = lean_usize_of_nat(v___x_6343_);
v___x_6348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6340_, v___x_6346_, v___x_6347_, v___x_6342_);
lean_dec_ref(v___x_6340_);
return v___x_6348_;
}
}
else
{
size_t v___x_6349_; size_t v___x_6350_; lean_object* v___x_6351_; 
v___x_6349_ = ((size_t)0ULL);
v___x_6350_ = lean_usize_of_nat(v___x_6343_);
v___x_6351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6340_, v___x_6349_, v___x_6350_, v___x_6342_);
lean_dec_ref(v___x_6340_);
return v___x_6351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6352_, size_t v_i_6353_, size_t v_stop_6354_, lean_object* v_b_6355_){
_start:
{
uint8_t v___x_6356_; 
v___x_6356_ = lean_usize_dec_eq(v_i_6353_, v_stop_6354_);
if (v___x_6356_ == 0)
{
lean_object* v___x_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; size_t v___x_6360_; size_t v___x_6361_; 
v___x_6357_ = lean_array_uget_borrowed(v_as_6352_, v_i_6353_);
lean_inc(v___x_6357_);
v___x_6358_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6357_);
v___x_6359_ = l_Array_append___redArg(v_b_6355_, v___x_6358_);
lean_dec_ref(v___x_6358_);
v___x_6360_ = ((size_t)1ULL);
v___x_6361_ = lean_usize_add(v_i_6353_, v___x_6360_);
v_i_6353_ = v___x_6361_;
v_b_6355_ = v___x_6359_;
goto _start;
}
else
{
return v_b_6355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6363_, lean_object* v_i_6364_, lean_object* v_stop_6365_, lean_object* v_b_6366_){
_start:
{
size_t v_i_boxed_6367_; size_t v_stop_boxed_6368_; lean_object* v_res_6369_; 
v_i_boxed_6367_ = lean_unbox_usize(v_i_6364_);
lean_dec(v_i_6364_);
v_stop_boxed_6368_ = lean_unbox_usize(v_stop_6365_);
lean_dec(v_stop_6365_);
v_res_6369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6363_, v_i_boxed_6367_, v_stop_boxed_6368_, v_b_6366_);
lean_dec_ref(v_as_6363_);
return v_res_6369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6370_){
_start:
{
lean_object* v___x_6371_; lean_object* v___x_6372_; lean_object* v___x_6373_; lean_object* v___x_6374_; lean_object* v___x_6375_; 
v___x_6371_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6372_ = lean_box(2);
v___x_6373_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6374_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6374_, 0, v___x_6372_);
lean_ctor_set(v___x_6374_, 1, v___x_6373_);
lean_ctor_set(v___x_6374_, 2, v_items_6370_);
v___x_6375_ = l_Lean_Syntax_node1(v___x_6372_, v___x_6371_, v___x_6374_);
return v___x_6375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6376_, lean_object* v_cfg_x27_6377_){
_start:
{
lean_object* v___x_6378_; lean_object* v___x_6379_; lean_object* v___x_6380_; lean_object* v___x_6381_; 
v___x_6378_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6376_);
v___x_6379_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6377_);
v___x_6380_ = l_Array_append___redArg(v___x_6378_, v___x_6379_);
lean_dec_ref(v___x_6379_);
v___x_6381_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6380_);
return v___x_6381_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_version_major = _init_l_Lean_version_major();
lean_mark_persistent(l_Lean_version_major);
l_Lean_version_minor = _init_l_Lean_version_minor();
lean_mark_persistent(l_Lean_version_minor);
l_Lean_version_patch = _init_l_Lean_version_patch();
lean_mark_persistent(l_Lean_version_patch);
l_Lean_githash = _init_l_Lean_githash();
lean_mark_persistent(l_Lean_githash);
l_Lean_version_isRelease = _init_l_Lean_version_isRelease();
l_Lean_version_specialDesc = _init_l_Lean_version_specialDesc();
lean_mark_persistent(l_Lean_version_specialDesc);
l_Lean_versionStringCore = _init_l_Lean_versionStringCore();
lean_mark_persistent(l_Lean_versionStringCore);
l_Lean_versionString = _init_l_Lean_versionString();
lean_mark_persistent(l_Lean_versionString);
l_Lean_toolchain = _init_l_Lean_toolchain();
lean_mark_persistent(l_Lean_toolchain);
l_Lean_idBeginEscape = _init_l_Lean_idBeginEscape();
l_Lean_idEndEscape = _init_l_Lean_idEndEscape();
l_Lean_Syntax_decodeQuotedChar___boxed__const__1 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__1);
l_Lean_Syntax_decodeQuotedChar___boxed__const__2 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__2);
l_Lean_Syntax_decodeQuotedChar___boxed__const__3 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__3);
l_Lean_Syntax_decodeQuotedChar___boxed__const__4 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__4);
l_Lean_Syntax_decodeQuotedChar___boxed__const__5 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__5);
l_Lean_Syntax_decodeQuotedChar___boxed__const__6 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__6);
l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1 = _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Meta_Defs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Meta_Defs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Meta_Defs(builtin);
}
#ifdef __cplusplus
}
#endif
