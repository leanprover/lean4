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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
uint32_t lean_string_front(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(lean_object*);
lean_object* lean_string_drop(lean_object*, lean_object*);
lean_object* lean_string_dropright(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_substring_beq(lean_object*, lean_object*);
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
lean_object* l_Lean_SourceInfo_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Char_quote(uint32_t);
lean_object* lean_string_trim(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0 = (const lean_object*)&l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg();
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg();
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg();
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg___boxed(lean_object*);
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
static const lean_closure_object l_Lean_Syntax_instBEqTSyntax___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_structEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instBEqTSyntax___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instBEqTSyntax___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg();
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_expandMacros___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_expandMacros___closed__0 = (const lean_object*)&l_Lean_expandMacros___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkMarkdownDocCommentFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_mkMarkdownDocCommentFrom___closed__0 = (const lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__0_value;
static const lean_string_object l_Lean_mkMarkdownDocCommentFrom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "commentBody"};
static const lean_object* l_Lean_mkMarkdownDocCommentFrom___closed__1 = (const lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__1_value;
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__2_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__2_value_aux_1),((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__2_value_aux_2),((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 50, 60, 220, 73, 28, 0, 197)}};
static const lean_object* l_Lean_mkMarkdownDocCommentFrom___closed__2 = (const lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__2_value;
static const lean_string_object l_Lean_mkMarkdownDocCommentFrom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-/"};
static const lean_object* l_Lean_mkMarkdownDocCommentFrom___closed__3 = (const lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__3_value;
static const lean_string_object l_Lean_mkMarkdownDocCommentFrom___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_mkMarkdownDocCommentFrom___closed__4 = (const lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__4_value;
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__5_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__5_value_aux_1),((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__5_value_aux_2),((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__4_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_mkMarkdownDocCommentFrom___closed__5 = (const lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__5_value;
static const lean_string_object l_Lean_mkMarkdownDocCommentFrom___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "/--"};
static const lean_object* l_Lean_mkMarkdownDocCommentFrom___closed__6 = (const lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocComment(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t, uint8_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1;
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
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_evalPrec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected precedence"};
static const lean_object* l_Lean_evalPrec___closed__0 = (const lean_object*)&l_Lean_evalPrec___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Syntax_instEmptyCollectionSepArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___closed__0;
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0;
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg();
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg();
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object*);
static const lean_string_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instCoeTermTSyntaxConsSyntaxNodeKindMkStr4Nil = (const lean_object*)&l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0_value;
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
uint32_t v___x_167_; uint8_t v___x_168_; 
v___x_167_ = 945;
v___x_168_ = lean_uint32_dec_le(v___x_167_, v_c_123_);
if (v___x_168_ == 0)
{
goto v___jp_158_;
}
else
{
uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_169_ = 969;
v___x_170_ = lean_uint32_dec_le(v_c_123_, v___x_169_);
if (v___x_170_ == 0)
{
goto v___jp_158_;
}
else
{
uint32_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = 955;
v___x_172_ = lean_uint32_dec_eq(v_c_123_, v___x_171_);
if (v___x_172_ == 0)
{
if (v___x_170_ == 0)
{
goto v___jp_158_;
}
else
{
return v___x_170_;
}
}
else
{
goto v___jp_158_;
}
}
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
uint32_t v___x_130_; uint8_t v___x_131_; 
v___x_130_ = 192;
v___x_131_ = lean_uint32_dec_le(v___x_130_, v_c_123_);
if (v___x_131_ == 0)
{
goto v___jp_124_;
}
else
{
uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 255;
v___x_133_ = lean_uint32_dec_le(v_c_123_, v___x_132_);
if (v___x_133_ == 0)
{
goto v___jp_124_;
}
else
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 215;
v___x_135_ = lean_uint32_dec_eq(v_c_123_, v___x_134_);
if (v___x_135_ == 0)
{
if (v___x_133_ == 0)
{
goto v___jp_124_;
}
else
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 247;
v___x_137_ = lean_uint32_dec_eq(v_c_123_, v___x_136_);
if (v___x_137_ == 0)
{
return v___x_133_;
}
else
{
goto v___jp_124_;
}
}
}
else
{
goto v___jp_124_;
}
}
}
}
v___jp_138_:
{
uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = 119964;
v___x_140_ = lean_uint32_dec_le(v___x_139_, v_c_123_);
if (v___x_140_ == 0)
{
goto v___jp_129_;
}
else
{
uint32_t v___x_141_; uint8_t v___x_142_; 
v___x_141_ = 120223;
v___x_142_ = lean_uint32_dec_le(v_c_123_, v___x_141_);
if (v___x_142_ == 0)
{
goto v___jp_129_;
}
else
{
return v___x_142_;
}
}
}
v___jp_143_:
{
uint32_t v___x_144_; uint8_t v___x_145_; 
v___x_144_ = 8448;
v___x_145_ = lean_uint32_dec_le(v___x_144_, v_c_123_);
if (v___x_145_ == 0)
{
goto v___jp_138_;
}
else
{
uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_146_ = 8527;
v___x_147_ = lean_uint32_dec_le(v_c_123_, v___x_146_);
if (v___x_147_ == 0)
{
goto v___jp_138_;
}
else
{
return v___x_147_;
}
}
}
v___jp_148_:
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 7936;
v___x_150_ = lean_uint32_dec_le(v___x_149_, v_c_123_);
if (v___x_150_ == 0)
{
goto v___jp_143_;
}
else
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 8190;
v___x_152_ = lean_uint32_dec_le(v_c_123_, v___x_151_);
if (v___x_152_ == 0)
{
goto v___jp_143_;
}
else
{
return v___x_152_;
}
}
}
v___jp_153_:
{
uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = 970;
v___x_155_ = lean_uint32_dec_le(v___x_154_, v_c_123_);
if (v___x_155_ == 0)
{
goto v___jp_148_;
}
else
{
uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 1019;
v___x_157_ = lean_uint32_dec_le(v_c_123_, v___x_156_);
if (v___x_157_ == 0)
{
goto v___jp_148_;
}
else
{
return v___x_157_;
}
}
}
v___jp_158_:
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 913;
v___x_160_ = lean_uint32_dec_le(v___x_159_, v_c_123_);
if (v___x_160_ == 0)
{
goto v___jp_153_;
}
else
{
uint32_t v___x_161_; uint8_t v___x_162_; 
v___x_161_ = 937;
v___x_162_ = lean_uint32_dec_le(v_c_123_, v___x_161_);
if (v___x_162_ == 0)
{
goto v___jp_153_;
}
else
{
uint32_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 928;
v___x_164_ = lean_uint32_dec_eq(v_c_123_, v___x_163_);
if (v___x_164_ == 0)
{
if (v___x_162_ == 0)
{
goto v___jp_153_;
}
else
{
uint32_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 931;
v___x_166_ = lean_uint32_dec_eq(v_c_123_, v___x_165_);
if (v___x_166_ == 0)
{
return v___x_162_;
}
else
{
goto v___jp_153_;
}
}
}
else
{
goto v___jp_153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLetterLike___boxed(lean_object* v_c_173_){
_start:
{
uint32_t v_c_boxed_174_; uint8_t v_res_175_; lean_object* v_r_176_; 
v_c_boxed_174_ = lean_unbox_uint32(v_c_173_);
lean_dec(v_c_173_);
v_res_175_ = l_Lean_isLetterLike(v_c_boxed_174_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNumericSubscript(uint32_t v_c_177_){
_start:
{
uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = 8320;
v___x_179_ = lean_uint32_dec_le(v___x_178_, v_c_177_);
if (v___x_179_ == 0)
{
return v___x_179_;
}
else
{
uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_180_ = 8329;
v___x_181_ = lean_uint32_dec_le(v_c_177_, v___x_180_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNumericSubscript___boxed(lean_object* v_c_182_){
_start:
{
uint32_t v_c_boxed_183_; uint8_t v_res_184_; lean_object* v_r_185_; 
v_c_boxed_183_ = lean_unbox_uint32(v_c_182_);
lean_dec(v_c_182_);
v_res_184_ = l_Lean_isNumericSubscript(v_c_boxed_183_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint8_t l_Lean_isSubScriptAlnum(uint32_t v_c_186_){
_start:
{
uint32_t v___x_200_; uint8_t v___x_201_; 
v___x_200_ = 8320;
v___x_201_ = lean_uint32_dec_le(v___x_200_, v_c_186_);
if (v___x_201_ == 0)
{
goto v___jp_195_;
}
else
{
uint32_t v___x_202_; uint8_t v___x_203_; 
v___x_202_ = 8329;
v___x_203_ = lean_uint32_dec_le(v_c_186_, v___x_202_);
if (v___x_203_ == 0)
{
goto v___jp_195_;
}
else
{
return v___x_203_;
}
}
v___jp_187_:
{
uint32_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = 11388;
v___x_189_ = lean_uint32_dec_eq(v_c_186_, v___x_188_);
return v___x_189_;
}
v___jp_190_:
{
uint32_t v___x_191_; uint8_t v___x_192_; 
v___x_191_ = 7522;
v___x_192_ = lean_uint32_dec_le(v___x_191_, v_c_186_);
if (v___x_192_ == 0)
{
goto v___jp_187_;
}
else
{
uint32_t v___x_193_; uint8_t v___x_194_; 
v___x_193_ = 7530;
v___x_194_ = lean_uint32_dec_le(v_c_186_, v___x_193_);
if (v___x_194_ == 0)
{
goto v___jp_187_;
}
else
{
return v___x_194_;
}
}
}
v___jp_195_:
{
uint32_t v___x_196_; uint8_t v___x_197_; 
v___x_196_ = 8336;
v___x_197_ = lean_uint32_dec_le(v___x_196_, v_c_186_);
if (v___x_197_ == 0)
{
goto v___jp_190_;
}
else
{
uint32_t v___x_198_; uint8_t v___x_199_; 
v___x_198_ = 8348;
v___x_199_ = lean_uint32_dec_le(v_c_186_, v___x_198_);
if (v___x_199_ == 0)
{
goto v___jp_190_;
}
else
{
return v___x_199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object* v_c_204_){
_start:
{
uint32_t v_c_boxed_205_; uint8_t v_res_206_; lean_object* v_r_207_; 
v_c_boxed_205_ = lean_unbox_uint32(v_c_204_);
lean_dec(v_c_204_);
v_res_206_ = l_Lean_isSubScriptAlnum(v_c_boxed_205_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirst(uint32_t v_c_208_){
_start:
{
uint8_t v___y_214_; uint32_t v___x_219_; uint8_t v___x_220_; 
v___x_219_ = 65;
v___x_220_ = lean_uint32_dec_le(v___x_219_, v_c_208_);
if (v___x_220_ == 0)
{
v___y_214_ = v___x_220_;
goto v___jp_213_;
}
else
{
uint32_t v___x_221_; uint8_t v___x_222_; 
v___x_221_ = 90;
v___x_222_ = lean_uint32_dec_le(v_c_208_, v___x_221_);
v___y_214_ = v___x_222_;
goto v___jp_213_;
}
v___jp_209_:
{
uint32_t v___x_210_; uint8_t v___x_211_; 
v___x_210_ = 95;
v___x_211_ = lean_uint32_dec_eq(v_c_208_, v___x_210_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; 
v___x_212_ = l_Lean_isLetterLike(v_c_208_);
return v___x_212_;
}
else
{
return v___x_211_;
}
}
v___jp_213_:
{
if (v___y_214_ == 0)
{
uint32_t v___x_215_; uint8_t v___x_216_; 
v___x_215_ = 97;
v___x_216_ = lean_uint32_dec_le(v___x_215_, v_c_208_);
if (v___x_216_ == 0)
{
goto v___jp_209_;
}
else
{
uint32_t v___x_217_; uint8_t v___x_218_; 
v___x_217_ = 122;
v___x_218_ = lean_uint32_dec_le(v_c_208_, v___x_217_);
if (v___x_218_ == 0)
{
goto v___jp_209_;
}
else
{
return v___x_218_;
}
}
}
else
{
return v___y_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirst___boxed(lean_object* v_c_223_){
_start:
{
uint32_t v_c_boxed_224_; uint8_t v_res_225_; lean_object* v_r_226_; 
v_c_boxed_224_ = lean_unbox_uint32(v_c_223_);
lean_dec(v_c_223_);
v_res_225_ = l_Lean_isIdFirst(v_c_boxed_224_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0(void){
_start:
{
uint32_t v___x_227_; uint8_t v___x_228_; 
v___x_227_ = 65;
v___x_228_ = lean_uint32_to_uint8(v___x_227_);
return v___x_228_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1(void){
_start:
{
uint32_t v___x_229_; uint8_t v___x_230_; 
v___x_229_ = 90;
v___x_230_ = lean_uint32_to_uint8(v___x_229_);
return v___x_230_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2(void){
_start:
{
uint32_t v___x_231_; uint8_t v___x_232_; 
v___x_231_ = 97;
v___x_232_ = lean_uint32_to_uint8(v___x_231_);
return v___x_232_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3(void){
_start:
{
uint32_t v___x_233_; uint8_t v___x_234_; 
v___x_233_ = 122;
v___x_234_ = lean_uint32_to_uint8(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t v_c_235_){
_start:
{
uint8_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_242_ = lean_uint8_dec_le(v___x_241_, v_c_235_);
if (v___x_242_ == 0)
{
goto v___jp_236_;
}
else
{
uint8_t v___x_243_; uint8_t v___x_244_; 
v___x_243_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_244_ = lean_uint8_dec_le(v_c_235_, v___x_243_);
if (v___x_244_ == 0)
{
goto v___jp_236_;
}
else
{
return v___x_244_;
}
}
v___jp_236_:
{
uint8_t v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_238_ = lean_uint8_dec_le(v___x_237_, v_c_235_);
if (v___x_238_ == 0)
{
return v___x_238_;
}
else
{
uint8_t v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_240_ = lean_uint8_dec_le(v_c_235_, v___x_239_);
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object* v_c_245_){
_start:
{
uint8_t v_c_boxed_246_; uint8_t v_res_247_; lean_object* v_r_248_; 
v_c_boxed_246_ = lean_unbox(v_c_245_);
v_res_247_ = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(v_c_boxed_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
static uint8_t _init_l_Lean_isIdFirstAscii___closed__0(void){
_start:
{
uint32_t v___x_249_; uint8_t v___x_250_; 
v___x_249_ = 95;
v___x_250_ = lean_uint32_to_uint8(v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirstAscii(uint8_t v_c_251_){
_start:
{
uint8_t v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_261_ = lean_uint8_dec_le(v___x_260_, v_c_251_);
if (v___x_261_ == 0)
{
goto v___jp_255_;
}
else
{
uint8_t v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_263_ = lean_uint8_dec_le(v_c_251_, v___x_262_);
if (v___x_263_ == 0)
{
goto v___jp_255_;
}
else
{
return v___x_263_;
}
}
v___jp_252_:
{
uint8_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_254_ = lean_uint8_dec_eq(v_c_251_, v___x_253_);
return v___x_254_;
}
v___jp_255_:
{
uint8_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_257_ = lean_uint8_dec_le(v___x_256_, v_c_251_);
if (v___x_257_ == 0)
{
goto v___jp_252_;
}
else
{
uint8_t v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_259_ = lean_uint8_dec_le(v_c_251_, v___x_258_);
if (v___x_259_ == 0)
{
goto v___jp_252_;
}
else
{
return v___x_259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object* v_c_264_){
_start:
{
uint8_t v_c_boxed_265_; uint8_t v_res_266_; lean_object* v_r_267_; 
v_c_boxed_265_ = lean_unbox(v_c_264_);
v_res_266_ = l_Lean_isIdFirstAscii(v_c_boxed_265_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0(void){
_start:
{
uint32_t v___x_268_; uint8_t v___x_269_; 
v___x_268_ = 48;
v___x_269_ = lean_uint32_to_uint8(v___x_268_);
return v___x_269_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1(void){
_start:
{
uint32_t v___x_270_; uint8_t v___x_271_; 
v___x_270_ = 57;
v___x_271_ = lean_uint32_to_uint8(v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t v_c_272_){
_start:
{
uint8_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_284_ = lean_uint8_dec_le(v___x_283_, v_c_272_);
if (v___x_284_ == 0)
{
goto v___jp_278_;
}
else
{
uint8_t v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_286_ = lean_uint8_dec_le(v_c_272_, v___x_285_);
if (v___x_286_ == 0)
{
goto v___jp_278_;
}
else
{
return v___x_286_;
}
}
v___jp_273_:
{
uint8_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_275_ = lean_uint8_dec_le(v___x_274_, v_c_272_);
if (v___x_275_ == 0)
{
return v___x_275_;
}
else
{
uint8_t v___x_276_; uint8_t v___x_277_; 
v___x_276_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_277_ = lean_uint8_dec_le(v_c_272_, v___x_276_);
return v___x_277_;
}
}
v___jp_278_:
{
uint8_t v___x_279_; uint8_t v___x_280_; 
v___x_279_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_280_ = lean_uint8_dec_le(v___x_279_, v_c_272_);
if (v___x_280_ == 0)
{
goto v___jp_273_;
}
else
{
uint8_t v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_282_ = lean_uint8_dec_le(v_c_272_, v___x_281_);
if (v___x_282_ == 0)
{
goto v___jp_273_;
}
else
{
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object* v_c_287_){
_start:
{
uint8_t v_c_boxed_288_; uint8_t v_res_289_; lean_object* v_r_290_; 
v_c_boxed_288_ = lean_unbox(v_c_287_);
v_res_289_ = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(v_c_boxed_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRest(uint32_t v_c_291_){
_start:
{
uint8_t v___y_309_; uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = 65;
v___x_315_ = lean_uint32_dec_le(v___x_314_, v_c_291_);
if (v___x_315_ == 0)
{
v___y_309_ = v___x_315_;
goto v___jp_308_;
}
else
{
uint32_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 90;
v___x_317_ = lean_uint32_dec_le(v_c_291_, v___x_316_);
v___y_309_ = v___x_317_;
goto v___jp_308_;
}
v___jp_292_:
{
uint32_t v___x_293_; uint8_t v___x_294_; 
v___x_293_ = 95;
v___x_294_ = lean_uint32_dec_eq(v_c_291_, v___x_293_);
if (v___x_294_ == 0)
{
uint32_t v___x_295_; uint8_t v___x_296_; 
v___x_295_ = 39;
v___x_296_ = lean_uint32_dec_eq(v_c_291_, v___x_295_);
if (v___x_296_ == 0)
{
uint32_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = 33;
v___x_298_ = lean_uint32_dec_eq(v_c_291_, v___x_297_);
if (v___x_298_ == 0)
{
uint32_t v___x_299_; uint8_t v___x_300_; 
v___x_299_ = 63;
v___x_300_ = lean_uint32_dec_eq(v_c_291_, v___x_299_);
if (v___x_300_ == 0)
{
uint8_t v___x_301_; 
v___x_301_ = l_Lean_isLetterLike(v_c_291_);
if (v___x_301_ == 0)
{
uint8_t v___x_302_; 
v___x_302_ = l_Lean_isSubScriptAlnum(v_c_291_);
return v___x_302_;
}
else
{
return v___x_301_;
}
}
else
{
return v___x_300_;
}
}
else
{
return v___x_298_;
}
}
else
{
return v___x_296_;
}
}
else
{
return v___x_294_;
}
}
v___jp_303_:
{
uint32_t v___x_304_; uint8_t v___x_305_; 
v___x_304_ = 48;
v___x_305_ = lean_uint32_dec_le(v___x_304_, v_c_291_);
if (v___x_305_ == 0)
{
goto v___jp_292_;
}
else
{
uint32_t v___x_306_; uint8_t v___x_307_; 
v___x_306_ = 57;
v___x_307_ = lean_uint32_dec_le(v_c_291_, v___x_306_);
if (v___x_307_ == 0)
{
goto v___jp_292_;
}
else
{
return v___x_307_;
}
}
}
v___jp_308_:
{
if (v___y_309_ == 0)
{
uint32_t v___x_310_; uint8_t v___x_311_; 
v___x_310_ = 97;
v___x_311_ = lean_uint32_dec_le(v___x_310_, v_c_291_);
if (v___x_311_ == 0)
{
goto v___jp_303_;
}
else
{
uint32_t v___x_312_; uint8_t v___x_313_; 
v___x_312_ = 122;
v___x_313_ = lean_uint32_dec_le(v_c_291_, v___x_312_);
if (v___x_313_ == 0)
{
goto v___jp_303_;
}
else
{
return v___x_313_;
}
}
}
else
{
return v___y_309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object* v_c_318_){
_start:
{
uint32_t v_c_boxed_319_; uint8_t v_res_320_; lean_object* v_r_321_; 
v_c_boxed_319_ = lean_unbox_uint32(v_c_318_);
lean_dec(v_c_318_);
v_res_320_ = l_Lean_isIdRest(v_c_boxed_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__0(void){
_start:
{
uint32_t v___x_322_; uint8_t v___x_323_; 
v___x_322_ = 39;
v___x_323_ = lean_uint32_to_uint8(v___x_322_);
return v___x_323_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__1(void){
_start:
{
uint32_t v___x_324_; uint8_t v___x_325_; 
v___x_324_ = 33;
v___x_325_ = lean_uint32_to_uint8(v___x_324_);
return v___x_325_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__2(void){
_start:
{
uint32_t v___x_326_; uint8_t v___x_327_; 
v___x_326_ = 63;
v___x_327_ = lean_uint32_to_uint8(v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRestAscii(uint8_t v_c_328_){
_start:
{
uint8_t v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_349_ = lean_uint8_dec_le(v___x_348_, v_c_328_);
if (v___x_349_ == 0)
{
goto v___jp_343_;
}
else
{
uint8_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_351_ = lean_uint8_dec_le(v_c_328_, v___x_350_);
if (v___x_351_ == 0)
{
goto v___jp_343_;
}
else
{
return v___x_351_;
}
}
v___jp_329_:
{
uint8_t v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_331_ = lean_uint8_dec_eq(v_c_328_, v___x_330_);
if (v___x_331_ == 0)
{
uint8_t v___x_332_; uint8_t v___x_333_; 
v___x_332_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__0, &l_Lean_isIdRestAscii___closed__0_once, _init_l_Lean_isIdRestAscii___closed__0);
v___x_333_ = lean_uint8_dec_eq(v_c_328_, v___x_332_);
if (v___x_333_ == 0)
{
uint8_t v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__1, &l_Lean_isIdRestAscii___closed__1_once, _init_l_Lean_isIdRestAscii___closed__1);
v___x_335_ = lean_uint8_dec_eq(v_c_328_, v___x_334_);
if (v___x_335_ == 0)
{
uint8_t v___x_336_; uint8_t v___x_337_; 
v___x_336_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__2, &l_Lean_isIdRestAscii___closed__2_once, _init_l_Lean_isIdRestAscii___closed__2);
v___x_337_ = lean_uint8_dec_eq(v_c_328_, v___x_336_);
return v___x_337_;
}
else
{
return v___x_335_;
}
}
else
{
return v___x_333_;
}
}
else
{
return v___x_331_;
}
}
v___jp_338_:
{
uint8_t v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_340_ = lean_uint8_dec_le(v___x_339_, v_c_328_);
if (v___x_340_ == 0)
{
goto v___jp_329_;
}
else
{
uint8_t v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_342_ = lean_uint8_dec_le(v_c_328_, v___x_341_);
if (v___x_342_ == 0)
{
goto v___jp_329_;
}
else
{
return v___x_342_;
}
}
}
v___jp_343_:
{
uint8_t v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_345_ = lean_uint8_dec_le(v___x_344_, v_c_328_);
if (v___x_345_ == 0)
{
goto v___jp_338_;
}
else
{
uint8_t v___x_346_; uint8_t v___x_347_; 
v___x_346_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_347_ = lean_uint8_dec_le(v_c_328_, v___x_346_);
if (v___x_347_ == 0)
{
goto v___jp_338_;
}
else
{
return v___x_347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRestAscii___boxed(lean_object* v_c_352_){
_start:
{
uint8_t v_c_boxed_353_; uint8_t v_res_354_; lean_object* v_r_355_; 
v_c_boxed_353_ = lean_unbox(v_c_352_);
v_res_354_ = l_Lean_isIdRestAscii(v_c_boxed_353_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
static uint32_t _init_l_Lean_idBeginEscape(void){
_start:
{
uint32_t v___x_356_; 
v___x_356_ = 171;
return v___x_356_;
}
}
static uint32_t _init_l_Lean_idEndEscape(void){
_start:
{
uint32_t v___x_357_; 
v___x_357_ = 187;
return v___x_357_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdBeginEscape(uint32_t v_c_358_){
_start:
{
uint32_t v___x_359_; uint8_t v___x_360_; 
v___x_359_ = 171;
v___x_360_ = lean_uint32_dec_eq(v_c_358_, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdBeginEscape___boxed(lean_object* v_c_361_){
_start:
{
uint32_t v_c_boxed_362_; uint8_t v_res_363_; lean_object* v_r_364_; 
v_c_boxed_362_ = lean_unbox_uint32(v_c_361_);
lean_dec(v_c_361_);
v_res_363_ = l_Lean_isIdBeginEscape(v_c_boxed_362_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdEndEscape(uint32_t v_c_365_){
_start:
{
uint32_t v___x_366_; uint8_t v___x_367_; 
v___x_366_ = 187;
v___x_367_ = lean_uint32_dec_eq(v_c_365_, v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdEndEscape___boxed(lean_object* v_c_368_){
_start:
{
uint32_t v_c_boxed_369_; uint8_t v_res_370_; lean_object* v_r_371_; 
v_c_boxed_369_ = lean_unbox_uint32(v_c_368_);
lean_dec(v_c_368_);
v_res_370_ = l_Lean_isIdEndEscape(v_c_boxed_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot(lean_object* v_x_372_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
return v_x_372_;
}
else
{
lean_object* v_pre_373_; 
v_pre_373_ = lean_ctor_get(v_x_372_, 0);
if (lean_obj_tag(v_pre_373_) == 0)
{
lean_inc(v_x_372_);
return v_x_372_;
}
else
{
v_x_372_ = v_pre_373_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot___boxed(lean_object* v_x_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Name_getRoot(v_x_375_);
lean_dec(v_x_375_);
return v_res_376_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInaccessibleUserName(lean_object* v_x_378_){
_start:
{
switch(lean_obj_tag(v_x_378_))
{
case 1:
{
lean_object* v_str_379_; uint32_t v___x_380_; uint8_t v___x_381_; 
v_str_379_ = lean_ctor_get(v_x_378_, 1);
lean_inc_ref_n(v_str_379_, 2);
lean_dec_ref_known(v_x_378_, 2);
v___x_380_ = 10013;
v___x_381_ = lean_string_contains(v_str_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = ((lean_object*)(l_Lean_Name_isInaccessibleUserName___closed__0));
v___x_383_ = lean_string_dec_eq(v_str_379_, v___x_382_);
lean_dec_ref(v_str_379_);
return v___x_383_;
}
else
{
lean_dec_ref(v_str_379_);
return v___x_381_;
}
}
case 2:
{
lean_object* v_pre_384_; 
v_pre_384_ = lean_ctor_get(v_x_378_, 0);
lean_inc(v_pre_384_);
lean_dec_ref_known(v_x_378_, 2);
v_x_378_ = v_pre_384_;
goto _start;
}
default: 
{
uint8_t v___x_386_; 
lean_dec(v_x_378_);
v___x_386_ = 0;
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInaccessibleUserName___boxed(lean_object* v_x_387_){
_start:
{
uint8_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_Lean_Name_isInaccessibleUserName(v_x_387_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(lean_object* v_s_390_, lean_object* v_i_391_){
_start:
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = lean_string_utf8_byte_size(v_s_390_);
v___x_397_ = lean_nat_dec_lt(v_i_391_, v___x_396_);
if (v___x_397_ == 0)
{
uint8_t v___x_398_; 
lean_dec(v_i_391_);
v___x_398_ = 1;
return v___x_398_;
}
else
{
uint8_t v_c_399_; uint8_t v___x_419_; uint8_t v___x_420_; 
lean_inc(v_i_391_);
v_c_399_ = lean_string_get_byte_fast(v_s_390_, v_i_391_);
v___x_419_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_420_ = lean_uint8_dec_le(v___x_419_, v_c_399_);
if (v___x_420_ == 0)
{
goto v___jp_414_;
}
else
{
uint8_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_422_ = lean_uint8_dec_le(v_c_399_, v___x_421_);
if (v___x_422_ == 0)
{
goto v___jp_414_;
}
else
{
goto v___jp_392_;
}
}
v___jp_400_:
{
uint8_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_402_ = lean_uint8_dec_eq(v_c_399_, v___x_401_);
if (v___x_402_ == 0)
{
uint8_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__0, &l_Lean_isIdRestAscii___closed__0_once, _init_l_Lean_isIdRestAscii___closed__0);
v___x_404_ = lean_uint8_dec_eq(v_c_399_, v___x_403_);
if (v___x_404_ == 0)
{
uint8_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__1, &l_Lean_isIdRestAscii___closed__1_once, _init_l_Lean_isIdRestAscii___closed__1);
v___x_406_ = lean_uint8_dec_eq(v_c_399_, v___x_405_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__2, &l_Lean_isIdRestAscii___closed__2_once, _init_l_Lean_isIdRestAscii___closed__2);
v___x_408_ = lean_uint8_dec_eq(v_c_399_, v___x_407_);
if (v___x_408_ == 0)
{
lean_dec(v_i_391_);
return v___x_408_;
}
else
{
goto v___jp_392_;
}
}
else
{
goto v___jp_392_;
}
}
else
{
goto v___jp_392_;
}
}
else
{
goto v___jp_392_;
}
}
v___jp_409_:
{
uint8_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_411_ = lean_uint8_dec_le(v___x_410_, v_c_399_);
if (v___x_411_ == 0)
{
goto v___jp_400_;
}
else
{
uint8_t v___x_412_; uint8_t v___x_413_; 
v___x_412_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_413_ = lean_uint8_dec_le(v_c_399_, v___x_412_);
if (v___x_413_ == 0)
{
goto v___jp_400_;
}
else
{
goto v___jp_392_;
}
}
}
v___jp_414_:
{
uint8_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_416_ = lean_uint8_dec_le(v___x_415_, v_c_399_);
if (v___x_416_ == 0)
{
goto v___jp_409_;
}
else
{
uint8_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_418_ = lean_uint8_dec_le(v_c_399_, v___x_417_);
if (v___x_418_ == 0)
{
goto v___jp_409_;
}
else
{
goto v___jp_392_;
}
}
}
}
v___jp_392_:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_nat_add(v_i_391_, v___x_393_);
lean_dec(v_i_391_);
v_i_391_ = v___x_394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object* v_s_423_, lean_object* v_i_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_423_, v_i_424_);
lean_dec_ref(v_s_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object* v_s_427_){
_start:
{
lean_object* v___x_431_; uint8_t v_c_432_; uint8_t v___x_441_; uint8_t v___x_442_; 
v___x_431_ = lean_unsigned_to_nat(0u);
v_c_432_ = lean_string_get_byte_fast(v_s_427_, v___x_431_);
v___x_441_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_442_ = lean_uint8_dec_le(v___x_441_, v_c_432_);
if (v___x_442_ == 0)
{
goto v___jp_436_;
}
else
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_444_ = lean_uint8_dec_le(v_c_432_, v___x_443_);
if (v___x_444_ == 0)
{
goto v___jp_436_;
}
else
{
goto v___jp_428_;
}
}
v___jp_428_:
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = lean_unsigned_to_nat(1u);
v___x_430_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_427_, v___x_429_);
return v___x_430_;
}
v___jp_433_:
{
uint8_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_435_ = lean_uint8_dec_eq(v_c_432_, v___x_434_);
if (v___x_435_ == 0)
{
return v___x_435_;
}
else
{
goto v___jp_428_;
}
}
v___jp_436_:
{
uint8_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_438_ = lean_uint8_dec_le(v___x_437_, v_c_432_);
if (v___x_438_ == 0)
{
goto v___jp_433_;
}
else
{
uint8_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_440_ = lean_uint8_dec_le(v_c_432_, v___x_439_);
if (v___x_440_ == 0)
{
goto v___jp_433_;
}
else
{
goto v___jp_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object* v_s_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_445_);
lean_dec_ref(v_s_445_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(lean_object* v_s_448_, lean_object* v_h_449_){
_start:
{
lean_object* v___x_453_; uint8_t v_c_454_; uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_453_ = lean_unsigned_to_nat(0u);
v_c_454_ = lean_string_get_byte_fast(v_s_448_, v___x_453_);
v___x_463_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_464_ = lean_uint8_dec_le(v___x_463_, v_c_454_);
if (v___x_464_ == 0)
{
goto v___jp_458_;
}
else
{
uint8_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_466_ = lean_uint8_dec_le(v_c_454_, v___x_465_);
if (v___x_466_ == 0)
{
goto v___jp_458_;
}
else
{
goto v___jp_450_;
}
}
v___jp_450_:
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_448_, v___x_451_);
return v___x_452_;
}
v___jp_455_:
{
uint8_t v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_457_ = lean_uint8_dec_eq(v_c_454_, v___x_456_);
if (v___x_457_ == 0)
{
return v___x_457_;
}
else
{
goto v___jp_450_;
}
}
v___jp_458_:
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_460_ = lean_uint8_dec_le(v___x_459_, v_c_454_);
if (v___x_460_ == 0)
{
goto v___jp_455_;
}
else
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_462_ = lean_uint8_dec_le(v_c_454_, v___x_461_);
if (v___x_462_ == 0)
{
goto v___jp_455_;
}
else
{
goto v___jp_450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object* v_s_467_, lean_object* v_h_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(v_s_467_, v_h_468_);
lean_dec_ref(v_s_467_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(lean_object* v_s_472_){
_start:
{
uint32_t v___y_482_; uint32_t v___y_487_; uint8_t v___y_488_; lean_object* v___x_503_; uint8_t v_c_504_; uint8_t v___x_513_; uint8_t v___x_514_; 
v___x_503_ = lean_unsigned_to_nat(0u);
v_c_504_ = lean_string_get_byte_fast(v_s_472_, v___x_503_);
v___x_513_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_514_ = lean_uint8_dec_le(v___x_513_, v_c_504_);
if (v___x_514_ == 0)
{
goto v___jp_508_;
}
else
{
uint8_t v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_516_ = lean_uint8_dec_le(v_c_504_, v___x_515_);
if (v___x_516_ == 0)
{
goto v___jp_508_;
}
else
{
goto v___jp_500_;
}
}
v___jp_473_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_string_utf8_byte_size(v_s_472_);
v___x_476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_476_, 0, v_s_472_);
lean_ctor_set(v___x_476_, 1, v___x_474_);
lean_ctor_set(v___x_476_, 2, v___x_475_);
v___x_477_ = lean_unsigned_to_nat(1u);
v___x_478_ = lean_substring_drop(v___x_476_, v___x_477_);
v___x_479_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_480_ = lean_substring_all(v___x_478_, v___x_479_);
return v___x_480_;
}
v___jp_481_:
{
uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 95;
v___x_484_ = lean_uint32_dec_eq(v___y_482_, v___x_483_);
if (v___x_484_ == 0)
{
uint8_t v___x_485_; 
v___x_485_ = l_Lean_isLetterLike(v___y_482_);
if (v___x_485_ == 0)
{
lean_dec_ref(v_s_472_);
return v___x_485_;
}
else
{
goto v___jp_473_;
}
}
else
{
goto v___jp_473_;
}
}
v___jp_486_:
{
if (v___y_488_ == 0)
{
uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_489_ = 97;
v___x_490_ = lean_uint32_dec_le(v___x_489_, v___y_487_);
if (v___x_490_ == 0)
{
v___y_482_ = v___y_487_;
goto v___jp_481_;
}
else
{
uint32_t v___x_491_; uint8_t v___x_492_; 
v___x_491_ = 122;
v___x_492_ = lean_uint32_dec_le(v___y_487_, v___x_491_);
if (v___x_492_ == 0)
{
v___y_482_ = v___y_487_;
goto v___jp_481_;
}
else
{
goto v___jp_473_;
}
}
}
else
{
goto v___jp_473_;
}
}
v___jp_493_:
{
lean_object* v___x_494_; uint32_t v___x_495_; uint32_t v___x_496_; uint8_t v___x_497_; 
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_string_utf8_get(v_s_472_, v___x_494_);
v___x_496_ = 65;
v___x_497_ = lean_uint32_dec_le(v___x_496_, v___x_495_);
if (v___x_497_ == 0)
{
v___y_487_ = v___x_495_;
v___y_488_ = v___x_497_;
goto v___jp_486_;
}
else
{
uint32_t v___x_498_; uint8_t v___x_499_; 
v___x_498_ = 90;
v___x_499_ = lean_uint32_dec_le(v___x_495_, v___x_498_);
v___y_487_ = v___x_495_;
v___y_488_ = v___x_499_;
goto v___jp_486_;
}
}
v___jp_500_:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_472_, v___x_501_);
if (v___x_502_ == 0)
{
goto v___jp_493_;
}
else
{
lean_dec_ref(v_s_472_);
return v___x_502_;
}
}
v___jp_505_:
{
uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_507_ = lean_uint8_dec_eq(v_c_504_, v___x_506_);
if (v___x_507_ == 0)
{
goto v___jp_493_;
}
else
{
goto v___jp_500_;
}
}
v___jp_508_:
{
uint8_t v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_510_ = lean_uint8_dec_le(v___x_509_, v_c_504_);
if (v___x_510_ == 0)
{
goto v___jp_505_;
}
else
{
uint8_t v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_512_ = lean_uint8_dec_le(v_c_504_, v___x_511_);
if (v___x_512_ == 0)
{
goto v___jp_505_;
}
else
{
goto v___jp_500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_517_){
_start:
{
uint8_t v_res_518_; lean_object* v_r_519_; 
v_res_518_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(v_s_517_);
v_r_519_ = lean_box(v_res_518_);
return v_r_519_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(lean_object* v_s_520_, lean_object* v_h_521_){
_start:
{
uint32_t v___y_531_; uint32_t v___y_536_; uint8_t v___y_537_; lean_object* v___x_552_; uint8_t v_c_553_; uint8_t v___x_562_; uint8_t v___x_563_; 
v___x_552_ = lean_unsigned_to_nat(0u);
v_c_553_ = lean_string_get_byte_fast(v_s_520_, v___x_552_);
v___x_562_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_563_ = lean_uint8_dec_le(v___x_562_, v_c_553_);
if (v___x_563_ == 0)
{
goto v___jp_557_;
}
else
{
uint8_t v___x_564_; uint8_t v___x_565_; 
v___x_564_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_565_ = lean_uint8_dec_le(v_c_553_, v___x_564_);
if (v___x_565_ == 0)
{
goto v___jp_557_;
}
else
{
goto v___jp_549_;
}
}
v___jp_522_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = lean_string_utf8_byte_size(v_s_520_);
v___x_525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_525_, 0, v_s_520_);
lean_ctor_set(v___x_525_, 1, v___x_523_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_substring_drop(v___x_525_, v___x_526_);
v___x_528_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_529_ = lean_substring_all(v___x_527_, v___x_528_);
return v___x_529_;
}
v___jp_530_:
{
uint32_t v___x_532_; uint8_t v___x_533_; 
v___x_532_ = 95;
v___x_533_ = lean_uint32_dec_eq(v___y_531_, v___x_532_);
if (v___x_533_ == 0)
{
uint8_t v___x_534_; 
v___x_534_ = l_Lean_isLetterLike(v___y_531_);
if (v___x_534_ == 0)
{
lean_dec_ref(v_s_520_);
return v___x_534_;
}
else
{
goto v___jp_522_;
}
}
else
{
goto v___jp_522_;
}
}
v___jp_535_:
{
if (v___y_537_ == 0)
{
uint32_t v___x_538_; uint8_t v___x_539_; 
v___x_538_ = 97;
v___x_539_ = lean_uint32_dec_le(v___x_538_, v___y_536_);
if (v___x_539_ == 0)
{
v___y_531_ = v___y_536_;
goto v___jp_530_;
}
else
{
uint32_t v___x_540_; uint8_t v___x_541_; 
v___x_540_ = 122;
v___x_541_ = lean_uint32_dec_le(v___y_536_, v___x_540_);
if (v___x_541_ == 0)
{
v___y_531_ = v___y_536_;
goto v___jp_530_;
}
else
{
goto v___jp_522_;
}
}
}
else
{
goto v___jp_522_;
}
}
v___jp_542_:
{
lean_object* v___x_543_; uint32_t v___x_544_; uint32_t v___x_545_; uint8_t v___x_546_; 
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_string_utf8_get(v_s_520_, v___x_543_);
v___x_545_ = 65;
v___x_546_ = lean_uint32_dec_le(v___x_545_, v___x_544_);
if (v___x_546_ == 0)
{
v___y_536_ = v___x_544_;
v___y_537_ = v___x_546_;
goto v___jp_535_;
}
else
{
uint32_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = 90;
v___x_548_ = lean_uint32_dec_le(v___x_544_, v___x_547_);
v___y_536_ = v___x_544_;
v___y_537_ = v___x_548_;
goto v___jp_535_;
}
}
v___jp_549_:
{
lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_520_, v___x_550_);
if (v___x_551_ == 0)
{
goto v___jp_542_;
}
else
{
lean_dec_ref(v_s_520_);
return v___x_551_;
}
}
v___jp_554_:
{
uint8_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_556_ = lean_uint8_dec_eq(v_c_553_, v___x_555_);
if (v___x_556_ == 0)
{
goto v___jp_542_;
}
else
{
goto v___jp_549_;
}
}
v___jp_557_:
{
uint8_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_559_ = lean_uint8_dec_le(v___x_558_, v_c_553_);
if (v___x_559_ == 0)
{
goto v___jp_554_;
}
else
{
uint8_t v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_561_ = lean_uint8_dec_le(v_c_553_, v___x_560_);
if (v___x_561_ == 0)
{
goto v___jp_554_;
}
else
{
goto v___jp_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_566_, lean_object* v_h_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(v_s_566_, v_h_567_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0(void){
_start:
{
uint32_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = 171;
v___x_571_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_572_ = lean_string_push(v___x_571_, v___x_570_);
return v___x_572_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1(void){
_start:
{
uint32_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = 187;
v___x_574_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_575_ = lean_string_push(v___x_574_, v___x_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape(lean_object* v_s_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_578_ = lean_string_append(v___x_577_, v_s_576_);
v___x_579_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_580_ = lean_string_append(v___x_578_, v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___boxed(lean_object* v_s_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Init_Meta_Defs_0__Lean_Name_escape(v_s_581_);
lean_dec_ref(v_s_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(lean_object* v_s_584_, uint8_t v_force_585_){
_start:
{
uint8_t v___y_596_; uint32_t v___y_607_; uint32_t v___y_612_; uint8_t v___y_613_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_string_utf8_byte_size(v_s_584_);
v___x_630_ = lean_nat_dec_lt(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_631_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_632_ = lean_string_append(v___x_631_, v_s_584_);
lean_dec_ref(v_s_584_);
v___x_633_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_634_ = lean_string_append(v___x_632_, v___x_633_);
v___x_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
else
{
if (v_force_585_ == 0)
{
uint8_t v_c_636_; uint8_t v___x_645_; uint8_t v___x_646_; 
v_c_636_ = lean_string_get_byte_fast(v_s_584_, v___x_628_);
v___x_645_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_646_ = lean_uint8_dec_le(v___x_645_, v_c_636_);
if (v___x_646_ == 0)
{
goto v___jp_640_;
}
else
{
uint8_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_648_ = lean_uint8_dec_le(v_c_636_, v___x_647_);
if (v___x_648_ == 0)
{
goto v___jp_640_;
}
else
{
goto v___jp_625_;
}
}
v___jp_637_:
{
uint8_t v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_639_ = lean_uint8_dec_eq(v_c_636_, v___x_638_);
if (v___x_639_ == 0)
{
goto v___jp_618_;
}
else
{
goto v___jp_625_;
}
}
v___jp_640_:
{
uint8_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_642_ = lean_uint8_dec_le(v___x_641_, v_c_636_);
if (v___x_642_ == 0)
{
goto v___jp_637_;
}
else
{
uint8_t v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_644_ = lean_uint8_dec_le(v_c_636_, v___x_643_);
if (v___x_644_ == 0)
{
goto v___jp_637_;
}
else
{
goto v___jp_625_;
}
}
}
}
else
{
goto v___jp_586_;
}
}
v___jp_586_:
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0));
lean_inc_ref(v_s_584_);
v___x_588_ = lean_string_any(v_s_584_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_589_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_590_ = lean_string_append(v___x_589_, v_s_584_);
lean_dec_ref(v_s_584_);
v___x_591_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_592_ = lean_string_append(v___x_590_, v___x_591_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
else
{
lean_object* v___x_594_; 
lean_dec_ref(v_s_584_);
v___x_594_ = lean_box(0);
return v___x_594_;
}
}
v___jp_595_:
{
if (v___y_596_ == 0)
{
goto v___jp_586_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_s_584_);
return v___x_597_;
}
}
v___jp_598_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_string_utf8_byte_size(v_s_584_);
lean_inc_ref(v_s_584_);
v___x_601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_601_, 0, v_s_584_);
lean_ctor_set(v___x_601_, 1, v___x_599_);
lean_ctor_set(v___x_601_, 2, v___x_600_);
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_substring_drop(v___x_601_, v___x_602_);
v___x_604_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_605_ = lean_substring_all(v___x_603_, v___x_604_);
v___y_596_ = v___x_605_;
goto v___jp_595_;
}
v___jp_606_:
{
uint32_t v___x_608_; uint8_t v___x_609_; 
v___x_608_ = 95;
v___x_609_ = lean_uint32_dec_eq(v___y_607_, v___x_608_);
if (v___x_609_ == 0)
{
uint8_t v___x_610_; 
v___x_610_ = l_Lean_isLetterLike(v___y_607_);
if (v___x_610_ == 0)
{
v___y_596_ = v___x_610_;
goto v___jp_595_;
}
else
{
goto v___jp_598_;
}
}
else
{
goto v___jp_598_;
}
}
v___jp_611_:
{
if (v___y_613_ == 0)
{
uint32_t v___x_614_; uint8_t v___x_615_; 
v___x_614_ = 97;
v___x_615_ = lean_uint32_dec_le(v___x_614_, v___y_612_);
if (v___x_615_ == 0)
{
v___y_607_ = v___y_612_;
goto v___jp_606_;
}
else
{
uint32_t v___x_616_; uint8_t v___x_617_; 
v___x_616_ = 122;
v___x_617_ = lean_uint32_dec_le(v___y_612_, v___x_616_);
if (v___x_617_ == 0)
{
v___y_607_ = v___y_612_;
goto v___jp_606_;
}
else
{
goto v___jp_598_;
}
}
}
else
{
goto v___jp_598_;
}
}
v___jp_618_:
{
lean_object* v___x_619_; uint32_t v___x_620_; uint32_t v___x_621_; uint8_t v___x_622_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_string_utf8_get(v_s_584_, v___x_619_);
v___x_621_ = 65;
v___x_622_ = lean_uint32_dec_le(v___x_621_, v___x_620_);
if (v___x_622_ == 0)
{
v___y_612_ = v___x_620_;
v___y_613_ = v___x_622_;
goto v___jp_611_;
}
else
{
uint32_t v___x_623_; uint8_t v___x_624_; 
v___x_623_ = 90;
v___x_624_ = lean_uint32_dec_le(v___x_620_, v___x_623_);
v___y_612_ = v___x_620_;
v___y_613_ = v___x_624_;
goto v___jp_611_;
}
}
v___jp_625_:
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_584_, v___x_626_);
if (v___x_627_ == 0)
{
goto v___jp_618_;
}
else
{
v___y_596_ = v___x_627_;
goto v___jp_595_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object* v_s_649_, lean_object* v_force_650_){
_start:
{
uint8_t v_force_boxed_651_; lean_object* v_res_652_; 
v_force_boxed_651_ = lean_unbox(v_force_650_);
v_res_652_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(v_s_649_, v_force_boxed_651_);
return v_res_652_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t v___y_653_){
_start:
{
uint32_t v___x_654_; uint8_t v___x_655_; 
v___x_654_ = 187;
v___x_655_ = lean_uint32_dec_eq(v___y_653_, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object* v___y_656_){
_start:
{
uint32_t v___y_284__boxed_657_; uint8_t v_res_658_; lean_object* v_r_659_; 
v___y_284__boxed_657_ = lean_unbox_uint32(v___y_656_);
lean_dec(v___y_656_);
v_res_658_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(v___y_284__boxed_657_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t v___y_660_){
_start:
{
uint8_t v___y_678_; uint32_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = 65;
v___x_684_ = lean_uint32_dec_le(v___x_683_, v___y_660_);
if (v___x_684_ == 0)
{
v___y_678_ = v___x_684_;
goto v___jp_677_;
}
else
{
uint32_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = 90;
v___x_686_ = lean_uint32_dec_le(v___y_660_, v___x_685_);
v___y_678_ = v___x_686_;
goto v___jp_677_;
}
v___jp_661_:
{
uint32_t v___x_662_; uint8_t v___x_663_; 
v___x_662_ = 95;
v___x_663_ = lean_uint32_dec_eq(v___y_660_, v___x_662_);
if (v___x_663_ == 0)
{
uint32_t v___x_664_; uint8_t v___x_665_; 
v___x_664_ = 39;
v___x_665_ = lean_uint32_dec_eq(v___y_660_, v___x_664_);
if (v___x_665_ == 0)
{
uint32_t v___x_666_; uint8_t v___x_667_; 
v___x_666_ = 33;
v___x_667_ = lean_uint32_dec_eq(v___y_660_, v___x_666_);
if (v___x_667_ == 0)
{
uint32_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = 63;
v___x_669_ = lean_uint32_dec_eq(v___y_660_, v___x_668_);
if (v___x_669_ == 0)
{
uint8_t v___x_670_; 
v___x_670_ = l_Lean_isLetterLike(v___y_660_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; 
v___x_671_ = l_Lean_isSubScriptAlnum(v___y_660_);
return v___x_671_;
}
else
{
return v___x_670_;
}
}
else
{
return v___x_669_;
}
}
else
{
return v___x_667_;
}
}
else
{
return v___x_665_;
}
}
else
{
return v___x_663_;
}
}
v___jp_672_:
{
uint32_t v___x_673_; uint8_t v___x_674_; 
v___x_673_ = 48;
v___x_674_ = lean_uint32_dec_le(v___x_673_, v___y_660_);
if (v___x_674_ == 0)
{
goto v___jp_661_;
}
else
{
uint32_t v___x_675_; uint8_t v___x_676_; 
v___x_675_ = 57;
v___x_676_ = lean_uint32_dec_le(v___y_660_, v___x_675_);
if (v___x_676_ == 0)
{
goto v___jp_661_;
}
else
{
return v___x_676_;
}
}
}
v___jp_677_:
{
if (v___y_678_ == 0)
{
uint32_t v___x_679_; uint8_t v___x_680_; 
v___x_679_ = 97;
v___x_680_ = lean_uint32_dec_le(v___x_679_, v___y_660_);
if (v___x_680_ == 0)
{
goto v___jp_672_;
}
else
{
uint32_t v___x_681_; uint8_t v___x_682_; 
v___x_681_ = 122;
v___x_682_ = lean_uint32_dec_le(v___y_660_, v___x_681_);
if (v___x_682_ == 0)
{
goto v___jp_672_;
}
else
{
return v___x_682_;
}
}
}
else
{
return v___y_678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object* v___y_687_){
_start:
{
uint32_t v___y_291__boxed_688_; uint8_t v_res_689_; lean_object* v_r_690_; 
v___y_291__boxed_688_ = lean_unbox_uint32(v___y_687_);
lean_dec(v___y_687_);
v_res_689_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(v___y_291__boxed_688_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t v_escape_693_, lean_object* v_s_694_, uint8_t v_force_695_){
_start:
{
if (v_escape_693_ == 0)
{
return v_s_694_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_string_utf8_byte_size(v_s_694_);
v___x_698_ = lean_nat_dec_lt(v___x_696_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_699_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_700_ = lean_string_append(v___x_699_, v_s_694_);
lean_dec_ref(v_s_694_);
v___x_701_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_702_ = lean_string_append(v___x_700_, v___x_701_);
return v___x_702_;
}
else
{
lean_object* v___f_703_; uint8_t v___y_711_; 
v___f_703_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
if (v_force_695_ == 0)
{
lean_object* v___f_712_; uint32_t v___y_719_; uint32_t v___y_724_; uint8_t v___y_725_; uint8_t v_c_739_; uint8_t v___x_748_; uint8_t v___x_749_; 
v___f_712_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_739_ = lean_string_get_byte_fast(v_s_694_, v___x_696_);
v___x_748_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_749_ = lean_uint8_dec_le(v___x_748_, v_c_739_);
if (v___x_749_ == 0)
{
goto v___jp_743_;
}
else
{
uint8_t v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_751_ = lean_uint8_dec_le(v_c_739_, v___x_750_);
if (v___x_751_ == 0)
{
goto v___jp_743_;
}
else
{
goto v___jp_736_;
}
}
v___jp_713_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
lean_inc_ref(v_s_694_);
v___x_714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_714_, 0, v_s_694_);
lean_ctor_set(v___x_714_, 1, v___x_696_);
lean_ctor_set(v___x_714_, 2, v___x_697_);
v___x_715_ = lean_unsigned_to_nat(1u);
v___x_716_ = lean_substring_drop(v___x_714_, v___x_715_);
v___x_717_ = lean_substring_all(v___x_716_, v___f_712_);
v___y_711_ = v___x_717_;
goto v___jp_710_;
}
v___jp_718_:
{
uint32_t v___x_720_; uint8_t v___x_721_; 
v___x_720_ = 95;
v___x_721_ = lean_uint32_dec_eq(v___y_719_, v___x_720_);
if (v___x_721_ == 0)
{
uint8_t v___x_722_; 
v___x_722_ = l_Lean_isLetterLike(v___y_719_);
if (v___x_722_ == 0)
{
v___y_711_ = v___x_722_;
goto v___jp_710_;
}
else
{
goto v___jp_713_;
}
}
else
{
goto v___jp_713_;
}
}
v___jp_723_:
{
if (v___y_725_ == 0)
{
uint32_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 97;
v___x_727_ = lean_uint32_dec_le(v___x_726_, v___y_724_);
if (v___x_727_ == 0)
{
v___y_719_ = v___y_724_;
goto v___jp_718_;
}
else
{
uint32_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 122;
v___x_729_ = lean_uint32_dec_le(v___y_724_, v___x_728_);
if (v___x_729_ == 0)
{
v___y_719_ = v___y_724_;
goto v___jp_718_;
}
else
{
goto v___jp_713_;
}
}
}
else
{
goto v___jp_713_;
}
}
v___jp_730_:
{
uint32_t v___x_731_; uint32_t v___x_732_; uint8_t v___x_733_; 
v___x_731_ = lean_string_utf8_get(v_s_694_, v___x_696_);
v___x_732_ = 65;
v___x_733_ = lean_uint32_dec_le(v___x_732_, v___x_731_);
if (v___x_733_ == 0)
{
v___y_724_ = v___x_731_;
v___y_725_ = v___x_733_;
goto v___jp_723_;
}
else
{
uint32_t v___x_734_; uint8_t v___x_735_; 
v___x_734_ = 90;
v___x_735_ = lean_uint32_dec_le(v___x_731_, v___x_734_);
v___y_724_ = v___x_731_;
v___y_725_ = v___x_735_;
goto v___jp_723_;
}
}
v___jp_736_:
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_694_, v___x_737_);
if (v___x_738_ == 0)
{
goto v___jp_730_;
}
else
{
v___y_711_ = v___x_738_;
goto v___jp_710_;
}
}
v___jp_740_:
{
uint8_t v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_742_ = lean_uint8_dec_eq(v_c_739_, v___x_741_);
if (v___x_742_ == 0)
{
goto v___jp_730_;
}
else
{
goto v___jp_736_;
}
}
v___jp_743_:
{
uint8_t v___x_744_; uint8_t v___x_745_; 
v___x_744_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_745_ = lean_uint8_dec_le(v___x_744_, v_c_739_);
if (v___x_745_ == 0)
{
goto v___jp_740_;
}
else
{
uint8_t v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_747_ = lean_uint8_dec_le(v_c_739_, v___x_746_);
if (v___x_747_ == 0)
{
goto v___jp_740_;
}
else
{
goto v___jp_736_;
}
}
}
}
else
{
goto v___jp_704_;
}
v___jp_704_:
{
uint8_t v___x_705_; 
lean_inc_ref(v_s_694_);
v___x_705_ = lean_string_any(v_s_694_, v___f_703_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_706_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_707_ = lean_string_append(v___x_706_, v_s_694_);
lean_dec_ref(v_s_694_);
v___x_708_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_709_ = lean_string_append(v___x_707_, v___x_708_);
return v___x_709_;
}
else
{
return v_s_694_;
}
}
v___jp_710_:
{
if (v___y_711_ == 0)
{
goto v___jp_704_;
}
else
{
return v_s_694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_752_, lean_object* v_s_753_, lean_object* v_force_754_){
_start:
{
uint8_t v_escape_boxed_755_; uint8_t v_force_boxed_756_; lean_object* v_res_757_; 
v_escape_boxed_755_ = lean_unbox(v_escape_752_);
v_force_boxed_756_ = lean_unbox(v_force_754_);
v_res_757_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_boxed_755_, v_s_753_, v_force_boxed_756_);
return v_res_757_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object* v_x_758_){
_start:
{
uint8_t v___x_759_; 
v___x_759_ = 0;
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed(lean_object* v_x_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(v_x_760_);
lean_dec_ref(v_x_760_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object* v_sep_765_, uint8_t v_escape_766_, lean_object* v_n_767_, lean_object* v_isToken_768_){
_start:
{
switch(lean_obj_tag(v_n_767_))
{
case 0:
{
lean_object* v___x_769_; 
lean_dec_ref(v_isToken_768_);
v___x_769_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_769_;
}
case 1:
{
lean_object* v_pre_770_; 
v_pre_770_ = lean_ctor_get(v_n_767_, 0);
if (lean_obj_tag(v_pre_770_) == 0)
{
lean_object* v_str_771_; lean_object* v___x_772_; uint8_t v___x_773_; lean_object* v___x_774_; 
v_str_771_ = lean_ctor_get(v_n_767_, 1);
lean_inc_ref_n(v_str_771_, 2);
lean_dec_ref_known(v_n_767_, 2);
v___x_772_ = lean_apply_1(v_isToken_768_, v_str_771_);
v___x_773_ = lean_unbox(v___x_772_);
v___x_774_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_766_, v_str_771_, v___x_773_);
return v___x_774_;
}
else
{
lean_object* v_str_775_; lean_object* v_r_776_; lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v_r_x27_780_; 
lean_inc(v_pre_770_);
v_str_775_ = lean_ctor_get(v_n_767_, 1);
lean_inc_ref_n(v_str_775_, 2);
lean_dec_ref_known(v_n_767_, 2);
lean_inc_ref(v_isToken_768_);
v_r_776_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_765_, v_escape_766_, v_pre_770_, v_isToken_768_);
v___x_777_ = lean_string_append(v_r_776_, v_sep_765_);
v___x_778_ = 0;
v___x_779_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_766_, v_str_775_, v___x_778_);
lean_inc_ref(v___x_777_);
v_r_x27_780_ = lean_string_append(v___x_777_, v___x_779_);
lean_dec_ref(v___x_779_);
if (v_escape_766_ == 0)
{
lean_dec_ref(v___x_777_);
lean_dec_ref(v_str_775_);
lean_dec_ref(v_isToken_768_);
return v_r_x27_780_;
}
else
{
lean_object* v___x_781_; uint8_t v___x_782_; 
lean_inc_ref(v_r_x27_780_);
v___x_781_ = lean_apply_1(v_isToken_768_, v_r_x27_780_);
v___x_782_ = lean_unbox(v___x_781_);
if (v___x_782_ == 0)
{
lean_dec_ref(v___x_777_);
lean_dec_ref(v_str_775_);
return v_r_x27_780_;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref(v_r_x27_780_);
v___x_783_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_766_, v_str_775_, v_escape_766_);
v___x_784_ = lean_string_append(v___x_777_, v___x_783_);
lean_dec_ref(v___x_783_);
return v___x_784_;
}
}
}
}
default: 
{
lean_object* v_pre_785_; 
lean_dec_ref(v_isToken_768_);
v_pre_785_ = lean_ctor_get(v_n_767_, 0);
if (lean_obj_tag(v_pre_785_) == 0)
{
lean_object* v_i_786_; lean_object* v___x_787_; 
v_i_786_ = lean_ctor_get(v_n_767_, 1);
lean_inc(v_i_786_);
lean_dec_ref_known(v_n_767_, 2);
v___x_787_ = l_Nat_reprFast(v_i_786_);
return v___x_787_;
}
else
{
lean_object* v_i_788_; lean_object* v___f_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_inc(v_pre_785_);
v_i_788_ = lean_ctor_get(v_n_767_, 1);
lean_inc(v_i_788_);
lean_dec_ref_known(v_n_767_, 2);
v___f_789_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1));
v___x_790_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_765_, v_escape_766_, v_pre_785_, v___f_789_);
v___x_791_ = lean_string_append(v___x_790_, v_sep_765_);
v___x_792_ = l_Nat_reprFast(v_i_788_);
v___x_793_ = lean_string_append(v___x_791_, v___x_792_);
lean_dec_ref(v___x_792_);
return v___x_793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object* v_sep_794_, lean_object* v_escape_795_, lean_object* v_n_796_, lean_object* v_isToken_797_){
_start:
{
uint8_t v_escape_boxed_798_; lean_object* v_res_799_; 
v_escape_boxed_798_ = lean_unbox(v_escape_795_);
v_res_799_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_794_, v_escape_boxed_798_, v_n_796_, v_isToken_797_);
lean_dec_ref(v_sep_794_);
return v_res_799_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object* v_n_805_){
_start:
{
lean_object* v___x_806_; uint8_t v___x_807_; uint8_t v___x_808_; 
v___x_806_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_807_ = lean_name_eq(v_n_805_, v___x_806_);
v___x_808_ = 1;
if (v___x_807_ == 0)
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_Name_getRoot(v_n_805_);
if (lean_obj_tag(v___x_809_) == 1)
{
lean_object* v_str_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_str_810_ = lean_ctor_get(v___x_809_, 1);
lean_inc_ref_n(v_str_810_, 2);
lean_dec_ref_known(v___x_809_, 2);
v___x_811_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_812_ = lean_string_isprefixof(v___x_811_, v_str_810_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3));
v___x_814_ = lean_string_isprefixof(v___x_813_, v_str_810_);
return v___x_814_;
}
else
{
lean_dec_ref(v_str_810_);
return v___x_808_;
}
}
else
{
lean_dec(v___x_809_);
return v___x_807_;
}
}
else
{
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_815_){
_start:
{
uint8_t v_res_816_; lean_object* v_r_817_; 
v_res_816_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_815_);
lean_dec(v_n_815_);
v_r_817_ = lean_box(v_res_816_);
return v_r_817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object* v_n_818_, uint8_t v_escape_819_, lean_object* v_isToken_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_819_ == 0)
{
lean_object* v___x_822_; 
v___x_822_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v_escape_819_, v_n_818_, v_isToken_820_);
return v___x_822_;
}
else
{
uint8_t v___x_823_; 
lean_inc(v_n_818_);
v___x_823_ = l_Lean_Name_isInaccessibleUserName(v_n_818_);
if (v___x_823_ == 0)
{
uint8_t v___x_824_; 
v___x_824_ = l_Lean_Name_hasMacroScopes(v_n_818_);
if (v___x_824_ == 0)
{
uint8_t v___x_825_; 
v___x_825_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_818_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; 
v___x_826_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v_escape_819_, v_n_818_, v_isToken_820_);
return v___x_826_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v___x_824_, v_n_818_, v_isToken_820_);
return v___x_827_;
}
}
else
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v___x_823_, v_n_818_, v_isToken_820_);
return v___x_828_;
}
}
else
{
uint8_t v___x_829_; lean_object* v___x_830_; 
v___x_829_ = 0;
v___x_830_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v___x_829_, v_n_818_, v_isToken_820_);
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object* v_n_831_, lean_object* v_escape_832_, lean_object* v_isToken_833_){
_start:
{
uint8_t v_escape_boxed_834_; lean_object* v_res_835_; 
v_escape_boxed_834_ = lean_unbox(v_escape_832_);
v_res_835_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(v_n_831_, v_escape_boxed_834_, v_isToken_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object* v_sep_836_, uint8_t v_escape_837_, lean_object* v_n_838_){
_start:
{
switch(lean_obj_tag(v_n_838_))
{
case 0:
{
lean_object* v___x_839_; 
v___x_839_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_839_;
}
case 1:
{
lean_object* v_pre_840_; 
v_pre_840_ = lean_ctor_get(v_n_838_, 0);
if (lean_obj_tag(v_pre_840_) == 0)
{
lean_object* v_str_841_; uint8_t v___x_842_; lean_object* v___x_843_; 
v_str_841_ = lean_ctor_get(v_n_838_, 1);
lean_inc_ref(v_str_841_);
lean_dec_ref_known(v_n_838_, 2);
v___x_842_ = 0;
v___x_843_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_837_, v_str_841_, v___x_842_);
return v___x_843_;
}
else
{
lean_object* v_str_844_; lean_object* v_r_845_; lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v_r_x27_849_; 
lean_inc(v_pre_840_);
v_str_844_ = lean_ctor_get(v_n_838_, 1);
lean_inc_ref(v_str_844_);
lean_dec_ref_known(v_n_838_, 2);
v_r_845_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_836_, v_escape_837_, v_pre_840_);
v___x_846_ = lean_string_append(v_r_845_, v_sep_836_);
v___x_847_ = 0;
v___x_848_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_837_, v_str_844_, v___x_847_);
v_r_x27_849_ = lean_string_append(v___x_846_, v___x_848_);
lean_dec_ref(v___x_848_);
return v_r_x27_849_;
}
}
default: 
{
lean_object* v_pre_850_; 
v_pre_850_ = lean_ctor_get(v_n_838_, 0);
if (lean_obj_tag(v_pre_850_) == 0)
{
lean_object* v_i_851_; lean_object* v___x_852_; 
v_i_851_ = lean_ctor_get(v_n_838_, 1);
lean_inc(v_i_851_);
lean_dec_ref_known(v_n_838_, 2);
v___x_852_ = l_Nat_reprFast(v_i_851_);
return v___x_852_;
}
else
{
lean_object* v_i_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_inc(v_pre_850_);
v_i_853_ = lean_ctor_get(v_n_838_, 1);
lean_inc(v_i_853_);
lean_dec_ref_known(v_n_838_, 2);
v___x_854_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_836_, v_escape_837_, v_pre_850_);
v___x_855_ = lean_string_append(v___x_854_, v_sep_836_);
v___x_856_ = l_Nat_reprFast(v_i_853_);
v___x_857_ = lean_string_append(v___x_855_, v___x_856_);
lean_dec_ref(v___x_856_);
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object* v_sep_858_, lean_object* v_escape_859_, lean_object* v_n_860_){
_start:
{
uint8_t v_escape_boxed_861_; lean_object* v_res_862_; 
v_escape_boxed_861_ = lean_unbox(v_escape_859_);
v_res_862_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_858_, v_escape_boxed_861_, v_n_860_);
lean_dec_ref(v_sep_858_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object* v_n_863_, uint8_t v_escape_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_864_ == 0)
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v_escape_864_, v_n_863_);
return v___x_866_;
}
else
{
uint8_t v___x_867_; 
lean_inc(v_n_863_);
v___x_867_ = l_Lean_Name_isInaccessibleUserName(v_n_863_);
if (v___x_867_ == 0)
{
uint8_t v___x_868_; 
v___x_868_ = l_Lean_Name_hasMacroScopes(v_n_863_);
if (v___x_868_ == 0)
{
uint8_t v___x_869_; 
v___x_869_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_863_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v_escape_864_, v_n_863_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; 
v___x_871_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v___x_868_, v_n_863_);
return v___x_871_;
}
}
else
{
lean_object* v___x_872_; 
v___x_872_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v___x_867_, v_n_863_);
return v___x_872_;
}
}
else
{
uint8_t v___x_873_; lean_object* v___x_874_; 
v___x_873_ = 0;
v___x_874_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v___x_873_, v_n_863_);
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object* v_n_875_, lean_object* v_escape_876_){
_start:
{
uint8_t v_escape_boxed_877_; lean_object* v_res_878_; 
v_escape_boxed_877_ = lean_unbox(v_escape_876_);
v_res_878_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_875_, v_escape_boxed_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object* v_n_879_, uint8_t v_escape_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_879_, v_escape_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object* v_n_882_, lean_object* v_escape_883_){
_start:
{
uint8_t v_escape_boxed_884_; lean_object* v_res_885_; 
v_escape_boxed_884_ = lean_unbox(v_escape_883_);
v_res_885_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(v_n_882_, v_escape_boxed_884_);
return v_res_885_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_hasNum(lean_object* v_x_886_){
_start:
{
switch(lean_obj_tag(v_x_886_))
{
case 0:
{
uint8_t v___x_887_; 
v___x_887_ = 0;
return v___x_887_;
}
case 1:
{
lean_object* v_pre_888_; 
v_pre_888_ = lean_ctor_get(v_x_886_, 0);
v_x_886_ = v_pre_888_;
goto _start;
}
default: 
{
uint8_t v___x_890_; 
v___x_890_ = 1;
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_hasNum___boxed(lean_object* v_x_891_){
_start:
{
uint8_t v_res_892_; lean_object* v_r_893_; 
v_res_892_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_x_891_);
lean_dec(v_x_891_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object* v_n_909_, lean_object* v_prec_910_){
_start:
{
switch(lean_obj_tag(v_n_909_))
{
case 0:
{
lean_object* v___x_911_; 
v___x_911_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__1));
return v___x_911_;
}
case 1:
{
lean_object* v_pre_912_; lean_object* v_str_913_; uint8_t v___x_914_; 
v_pre_912_ = lean_ctor_get(v_n_909_, 0);
v_str_913_ = lean_ctor_get(v_n_909_, 1);
v___x_914_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_pre_912_);
if (v___x_914_ == 0)
{
uint8_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_915_ = 1;
v___x_916_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__3));
v___x_917_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_909_, v___x_915_);
v___x_918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
v___x_919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_916_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
return v___x_919_;
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_inc_ref(v_str_913_);
lean_inc(v_pre_912_);
lean_dec_ref_known(v_n_909_, 2);
v___x_920_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__5));
v___x_921_ = lean_unsigned_to_nat(1024u);
v___x_922_ = l_Lean_Name_reprPrec(v_pre_912_, v___x_921_);
v___x_923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_920_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = l_String_quote(v_str_913_);
v___x_927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
v___x_928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_925_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Repr_addAppParen(v___x_928_, v_prec_910_);
return v___x_929_;
}
}
default: 
{
lean_object* v_pre_930_; lean_object* v_i_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_pre_930_ = lean_ctor_get(v_n_909_, 0);
lean_inc(v_pre_930_);
v_i_931_ = lean_ctor_get(v_n_909_, 1);
lean_inc(v_i_931_);
lean_dec_ref_known(v_n_909_, 2);
v___x_932_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__9));
v___x_933_ = lean_unsigned_to_nat(1024u);
v___x_934_ = l_Lean_Name_reprPrec(v_pre_930_, v___x_933_);
v___x_935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_932_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Nat_reprFast(v_i_931_);
v___x_939_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
v___x_940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_937_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = l_Repr_addAppParen(v___x_940_, v_prec_910_);
return v___x_941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object* v_n_942_, lean_object* v_prec_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Name_reprPrec(v_n_942_, v_prec_943_);
lean_dec(v_prec_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object* v_x_947_){
_start:
{
if (lean_obj_tag(v_x_947_) == 1)
{
lean_object* v_pre_948_; lean_object* v_str_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_pre_948_ = lean_ctor_get(v_x_947_, 0);
lean_inc(v_pre_948_);
v_str_949_ = lean_ctor_get(v_x_947_, 1);
lean_inc_ref(v_str_949_);
lean_dec_ref_known(v_x_947_, 2);
v___x_950_ = lean_string_capitalize(v_str_949_);
v___x_951_ = l_Lean_Name_str___override(v_pre_948_, v___x_950_);
return v___x_951_;
}
else
{
return v_x_947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
switch(lean_obj_tag(v_x_952_))
{
case 0:
{
if (lean_obj_tag(v_x_953_) == 0)
{
lean_inc(v_x_954_);
return v_x_954_;
}
else
{
return v_x_952_;
}
}
case 1:
{
lean_object* v_pre_955_; lean_object* v_str_956_; uint8_t v___x_957_; 
v_pre_955_ = lean_ctor_get(v_x_952_, 0);
lean_inc(v_pre_955_);
v_str_956_ = lean_ctor_get(v_x_952_, 1);
lean_inc_ref(v_str_956_);
v___x_957_ = lean_name_eq(v_x_952_, v_x_953_);
lean_dec_ref_known(v_x_952_, 2);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = l_Lean_Name_replacePrefix(v_pre_955_, v_x_953_, v_x_954_);
v___x_959_ = l_Lean_Name_str___override(v___x_958_, v_str_956_);
return v___x_959_;
}
else
{
lean_dec_ref(v_str_956_);
lean_dec(v_pre_955_);
lean_inc(v_x_954_);
return v_x_954_;
}
}
default: 
{
lean_object* v_pre_960_; lean_object* v_i_961_; uint8_t v___x_962_; 
v_pre_960_ = lean_ctor_get(v_x_952_, 0);
lean_inc(v_pre_960_);
v_i_961_ = lean_ctor_get(v_x_952_, 1);
lean_inc(v_i_961_);
v___x_962_ = lean_name_eq(v_x_952_, v_x_953_);
lean_dec_ref_known(v_x_952_, 2);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = l_Lean_Name_replacePrefix(v_pre_960_, v_x_953_, v_x_954_);
v___x_964_ = l_Lean_Name_num___override(v___x_963_, v_i_961_);
return v___x_964_;
}
else
{
lean_dec(v_i_961_);
lean_dec(v_pre_960_);
lean_inc(v_x_954_);
return v_x_954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Name_replacePrefix(v_x_965_, v_x_966_, v_x_967_);
lean_dec(v_x_967_);
lean_dec(v_x_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
switch(lean_obj_tag(v_x_970_))
{
case 0:
{
lean_object* v___x_971_; 
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v_x_969_);
return v___x_971_;
}
case 1:
{
if (lean_obj_tag(v_x_969_) == 1)
{
lean_object* v_pre_972_; lean_object* v_str_973_; lean_object* v_pre_974_; lean_object* v_str_975_; uint8_t v___x_976_; 
v_pre_972_ = lean_ctor_get(v_x_970_, 0);
v_str_973_ = lean_ctor_get(v_x_970_, 1);
v_pre_974_ = lean_ctor_get(v_x_969_, 0);
lean_inc(v_pre_974_);
v_str_975_ = lean_ctor_get(v_x_969_, 1);
lean_inc_ref(v_str_975_);
lean_dec_ref_known(v_x_969_, 2);
v___x_976_ = lean_string_dec_eq(v_str_975_, v_str_973_);
lean_dec_ref(v_str_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
lean_dec(v_pre_974_);
v___x_977_ = lean_box(0);
return v___x_977_;
}
else
{
v_x_969_ = v_pre_974_;
v_x_970_ = v_pre_972_;
goto _start;
}
}
else
{
lean_object* v___x_979_; 
lean_dec(v_x_969_);
v___x_979_ = lean_box(0);
return v___x_979_;
}
}
default: 
{
if (lean_obj_tag(v_x_969_) == 2)
{
lean_object* v_pre_980_; lean_object* v_i_981_; lean_object* v_pre_982_; lean_object* v_i_983_; uint8_t v___x_984_; 
v_pre_980_ = lean_ctor_get(v_x_970_, 0);
v_i_981_ = lean_ctor_get(v_x_970_, 1);
v_pre_982_ = lean_ctor_get(v_x_969_, 0);
lean_inc(v_pre_982_);
v_i_983_ = lean_ctor_get(v_x_969_, 1);
lean_inc(v_i_983_);
lean_dec_ref_known(v_x_969_, 2);
v___x_984_ = lean_nat_dec_eq(v_i_983_, v_i_981_);
lean_dec(v_i_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
lean_dec(v_pre_982_);
v___x_985_ = lean_box(0);
return v___x_985_;
}
else
{
v_x_969_ = v_pre_982_;
v_x_970_ = v_pre_980_;
goto _start;
}
}
else
{
lean_object* v___x_987_; 
lean_dec(v_x_969_);
v___x_987_ = lean_box(0);
return v___x_987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object* v_x_988_, lean_object* v_x_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Name_eraseSuffix_x3f(v_x_988_, v_x_989_);
lean_dec(v_x_989_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object* v_n_991_, lean_object* v_f_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = l_Lean_Name_hasMacroScopes(v_n_991_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
v___x_994_ = lean_apply_1(v_f_992_, v_n_991_);
return v___x_994_;
}
else
{
lean_object* v_view_995_; lean_object* v_name_996_; lean_object* v_imported_997_; lean_object* v_ctx_998_; lean_object* v_scopes_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1008_; 
v_view_995_ = l_Lean_extractMacroScopes(v_n_991_);
v_name_996_ = lean_ctor_get(v_view_995_, 0);
v_imported_997_ = lean_ctor_get(v_view_995_, 1);
v_ctx_998_ = lean_ctor_get(v_view_995_, 2);
v_scopes_999_ = lean_ctor_get(v_view_995_, 3);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_view_995_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1001_ = v_view_995_;
v_isShared_1002_ = v_isSharedCheck_1008_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_scopes_999_);
lean_inc(v_ctx_998_);
lean_inc(v_imported_997_);
lean_inc(v_name_996_);
lean_dec(v_view_995_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1008_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = lean_apply_1(v_f_992_, v_name_996_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1003_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_imported_997_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_ctx_998_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v_scopes_999_);
v___x_1005_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_MacroScopesView_review(v___x_1005_);
return v___x_1006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object* v_suffix_1009_, lean_object* v_x_1010_){
_start:
{
if (lean_obj_tag(v_x_1010_) == 1)
{
lean_object* v_pre_1011_; lean_object* v_str_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_pre_1011_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_pre_1011_);
v_str_1012_ = lean_ctor_get(v_x_1010_, 1);
lean_inc_ref(v_str_1012_);
lean_dec_ref_known(v_x_1010_, 2);
v___x_1013_ = lean_string_append(v_str_1012_, v_suffix_1009_);
lean_dec_ref(v_suffix_1009_);
v___x_1014_ = l_Lean_Name_str___override(v_pre_1011_, v___x_1013_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_Name_str___override(v_x_1010_, v_suffix_1009_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_after(lean_object* v_n_1016_, lean_object* v_suffix_1017_){
_start:
{
uint8_t v___x_1018_; 
v___x_1018_ = l_Lean_Name_hasMacroScopes(v_n_1016_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_Name_appendAfter___lam__0(v_suffix_1017_, v_n_1016_);
return v___x_1019_;
}
else
{
lean_object* v_view_1020_; lean_object* v_name_1021_; lean_object* v_imported_1022_; lean_object* v_ctx_1023_; lean_object* v_scopes_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1033_; 
v_view_1020_ = l_Lean_extractMacroScopes(v_n_1016_);
v_name_1021_ = lean_ctor_get(v_view_1020_, 0);
v_imported_1022_ = lean_ctor_get(v_view_1020_, 1);
v_ctx_1023_ = lean_ctor_get(v_view_1020_, 2);
v_scopes_1024_ = lean_ctor_get(v_view_1020_, 3);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_view_1020_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1026_ = v_view_1020_;
v_isShared_1027_ = v_isSharedCheck_1033_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_scopes_1024_);
lean_inc(v_ctx_1023_);
lean_inc(v_imported_1022_);
lean_inc(v_name_1021_);
lean_dec(v_view_1020_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1033_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = l_Lean_Name_appendAfter___lam__0(v_suffix_1017_, v_name_1021_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1028_);
v___x_1030_ = v___x_1026_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_imported_1022_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_ctx_1023_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_scopes_1024_);
v___x_1030_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_MacroScopesView_review(v___x_1030_);
return v___x_1031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object* v_idx_1034_, lean_object* v_x_1035_){
_start:
{
if (lean_obj_tag(v_x_1035_) == 1)
{
lean_object* v_pre_1036_; lean_object* v_str_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_pre_1036_ = lean_ctor_get(v_x_1035_, 0);
lean_inc(v_pre_1036_);
v_str_1037_ = lean_ctor_get(v_x_1035_, 1);
lean_inc_ref(v_str_1037_);
lean_dec_ref_known(v_x_1035_, 2);
v___x_1038_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1039_ = lean_string_append(v_str_1037_, v___x_1038_);
v___x_1040_ = l_Nat_reprFast(v_idx_1034_);
v___x_1041_ = lean_string_append(v___x_1039_, v___x_1040_);
lean_dec_ref(v___x_1040_);
v___x_1042_ = l_Lean_Name_str___override(v_pre_1036_, v___x_1041_);
return v___x_1042_;
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1043_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1044_ = l_Nat_reprFast(v_idx_1034_);
v___x_1045_ = lean_string_append(v___x_1043_, v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = l_Lean_Name_str___override(v_x_1035_, v___x_1045_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object* v_n_1047_, lean_object* v_idx_1048_){
_start:
{
uint8_t v___x_1049_; 
v___x_1049_ = l_Lean_Name_hasMacroScopes(v_n_1047_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1048_, v_n_1047_);
return v___x_1050_;
}
else
{
lean_object* v_view_1051_; lean_object* v_name_1052_; lean_object* v_imported_1053_; lean_object* v_ctx_1054_; lean_object* v_scopes_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1064_; 
v_view_1051_ = l_Lean_extractMacroScopes(v_n_1047_);
v_name_1052_ = lean_ctor_get(v_view_1051_, 0);
v_imported_1053_ = lean_ctor_get(v_view_1051_, 1);
v_ctx_1054_ = lean_ctor_get(v_view_1051_, 2);
v_scopes_1055_ = lean_ctor_get(v_view_1051_, 3);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_view_1051_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1057_ = v_view_1051_;
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_scopes_1055_);
lean_inc(v_ctx_1054_);
lean_inc(v_imported_1053_);
lean_inc(v_name_1052_);
lean_dec(v_view_1051_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1048_, v_name_1052_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1059_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_imported_1053_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_ctx_1054_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v_scopes_1055_);
v___x_1061_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_MacroScopesView_review(v___x_1061_);
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object* v_pre_1065_, lean_object* v_x_1066_){
_start:
{
switch(lean_obj_tag(v_x_1066_))
{
case 0:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Name_str___override(v_x_1066_, v_pre_1065_);
return v___x_1067_;
}
case 1:
{
lean_object* v_pre_1068_; lean_object* v_str_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_pre_1068_ = lean_ctor_get(v_x_1066_, 0);
lean_inc(v_pre_1068_);
v_str_1069_ = lean_ctor_get(v_x_1066_, 1);
lean_inc_ref(v_str_1069_);
lean_dec_ref_known(v_x_1066_, 2);
v___x_1070_ = lean_string_append(v_pre_1065_, v_str_1069_);
lean_dec_ref(v_str_1069_);
v___x_1071_ = l_Lean_Name_str___override(v_pre_1068_, v___x_1070_);
return v___x_1071_;
}
default: 
{
lean_object* v_pre_1072_; lean_object* v_i_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_pre_1072_ = lean_ctor_get(v_x_1066_, 0);
lean_inc(v_pre_1072_);
v_i_1073_ = lean_ctor_get(v_x_1066_, 1);
lean_inc(v_i_1073_);
lean_dec_ref_known(v_x_1066_, 2);
v___x_1074_ = l_Lean_Name_str___override(v_pre_1072_, v_pre_1065_);
v___x_1075_ = l_Lean_Name_num___override(v___x_1074_, v_i_1073_);
return v___x_1075_;
}
}
}
}
LEAN_EXPORT lean_object* lean_name_append_before(lean_object* v_n_1076_, lean_object* v_pre_1077_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = l_Lean_Name_hasMacroScopes(v_n_1076_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Name_appendBefore___lam__0(v_pre_1077_, v_n_1076_);
return v___x_1079_;
}
else
{
lean_object* v_view_1080_; lean_object* v_name_1081_; lean_object* v_imported_1082_; lean_object* v_ctx_1083_; lean_object* v_scopes_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1093_; 
v_view_1080_ = l_Lean_extractMacroScopes(v_n_1076_);
v_name_1081_ = lean_ctor_get(v_view_1080_, 0);
v_imported_1082_ = lean_ctor_get(v_view_1080_, 1);
v_ctx_1083_ = lean_ctor_get(v_view_1080_, 2);
v_scopes_1084_ = lean_ctor_get(v_view_1080_, 3);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_view_1080_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1086_ = v_view_1080_;
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_scopes_1084_);
lean_inc(v_ctx_1083_);
lean_inc(v_imported_1082_);
lean_inc(v_name_1081_);
lean_dec(v_view_1080_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1088_ = l_Lean_Name_appendBefore___lam__0(v_pre_1077_, v_name_1081_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1088_);
v___x_1090_ = v___x_1086_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_imported_1082_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_ctx_1083_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_scopes_1084_);
v___x_1090_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_MacroScopesView_review(v___x_1090_);
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object* v_x_1094_, lean_object* v_x_1095_, lean_object* v_h__1_1096_, lean_object* v_h__2_1097_, lean_object* v_h__3_1098_, lean_object* v_h__4_1099_){
_start:
{
switch(lean_obj_tag(v_x_1094_))
{
case 0:
{
lean_dec(v_h__3_1098_);
lean_dec(v_h__2_1097_);
if (lean_obj_tag(v_x_1095_) == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_h__4_1099_);
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_apply_1(v_h__1_1096_, v___x_1100_);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; 
lean_dec(v_h__1_1096_);
v___x_1102_ = lean_apply_5(v_h__4_1099_, v_x_1094_, v_x_1095_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1102_;
}
}
case 1:
{
lean_dec(v_h__3_1098_);
lean_dec(v_h__1_1096_);
if (lean_obj_tag(v_x_1095_) == 1)
{
lean_object* v_pre_1103_; lean_object* v_str_1104_; lean_object* v_pre_1105_; lean_object* v_str_1106_; lean_object* v___x_1107_; 
lean_dec(v_h__4_1099_);
v_pre_1103_ = lean_ctor_get(v_x_1094_, 0);
lean_inc(v_pre_1103_);
v_str_1104_ = lean_ctor_get(v_x_1094_, 1);
lean_inc_ref(v_str_1104_);
lean_dec_ref_known(v_x_1094_, 2);
v_pre_1105_ = lean_ctor_get(v_x_1095_, 0);
lean_inc(v_pre_1105_);
v_str_1106_ = lean_ctor_get(v_x_1095_, 1);
lean_inc_ref(v_str_1106_);
lean_dec_ref_known(v_x_1095_, 2);
v___x_1107_ = lean_apply_4(v_h__2_1097_, v_pre_1103_, v_str_1104_, v_pre_1105_, v_str_1106_);
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; 
lean_dec(v_h__2_1097_);
v___x_1108_ = lean_apply_5(v_h__4_1099_, v_x_1094_, v_x_1095_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1108_;
}
}
default: 
{
lean_dec(v_h__2_1097_);
lean_dec(v_h__1_1096_);
if (lean_obj_tag(v_x_1095_) == 2)
{
lean_object* v_pre_1109_; lean_object* v_i_1110_; lean_object* v_pre_1111_; lean_object* v_i_1112_; lean_object* v___x_1113_; 
lean_dec(v_h__4_1099_);
v_pre_1109_ = lean_ctor_get(v_x_1094_, 0);
lean_inc(v_pre_1109_);
v_i_1110_ = lean_ctor_get(v_x_1094_, 1);
lean_inc(v_i_1110_);
lean_dec_ref_known(v_x_1094_, 2);
v_pre_1111_ = lean_ctor_get(v_x_1095_, 0);
lean_inc(v_pre_1111_);
v_i_1112_ = lean_ctor_get(v_x_1095_, 1);
lean_inc(v_i_1112_);
lean_dec_ref_known(v_x_1095_, 2);
v___x_1113_ = lean_apply_4(v_h__3_1098_, v_pre_1109_, v_i_1110_, v_pre_1111_, v_i_1112_);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; 
lean_dec(v_h__3_1098_);
v___x_1114_ = lean_apply_5(v_h__4_1099_, v_x_1094_, v_x_1095_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object* v_motive_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_h__1_1118_, lean_object* v_h__2_1119_, lean_object* v_h__3_1120_, lean_object* v_h__4_1121_){
_start:
{
switch(lean_obj_tag(v_x_1116_))
{
case 0:
{
lean_dec(v_h__3_1120_);
lean_dec(v_h__2_1119_);
if (lean_obj_tag(v_x_1117_) == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec(v_h__4_1121_);
v___x_1122_ = lean_box(0);
v___x_1123_ = lean_apply_1(v_h__1_1118_, v___x_1122_);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; 
lean_dec(v_h__1_1118_);
v___x_1124_ = lean_apply_5(v_h__4_1121_, v_x_1116_, v_x_1117_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1124_;
}
}
case 1:
{
lean_dec(v_h__3_1120_);
lean_dec(v_h__1_1118_);
if (lean_obj_tag(v_x_1117_) == 1)
{
lean_object* v_pre_1125_; lean_object* v_str_1126_; lean_object* v_pre_1127_; lean_object* v_str_1128_; lean_object* v___x_1129_; 
lean_dec(v_h__4_1121_);
v_pre_1125_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_pre_1125_);
v_str_1126_ = lean_ctor_get(v_x_1116_, 1);
lean_inc_ref(v_str_1126_);
lean_dec_ref_known(v_x_1116_, 2);
v_pre_1127_ = lean_ctor_get(v_x_1117_, 0);
lean_inc(v_pre_1127_);
v_str_1128_ = lean_ctor_get(v_x_1117_, 1);
lean_inc_ref(v_str_1128_);
lean_dec_ref_known(v_x_1117_, 2);
v___x_1129_ = lean_apply_4(v_h__2_1119_, v_pre_1125_, v_str_1126_, v_pre_1127_, v_str_1128_);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; 
lean_dec(v_h__2_1119_);
v___x_1130_ = lean_apply_5(v_h__4_1121_, v_x_1116_, v_x_1117_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1130_;
}
}
default: 
{
lean_dec(v_h__2_1119_);
lean_dec(v_h__1_1118_);
if (lean_obj_tag(v_x_1117_) == 2)
{
lean_object* v_pre_1131_; lean_object* v_i_1132_; lean_object* v_pre_1133_; lean_object* v_i_1134_; lean_object* v___x_1135_; 
lean_dec(v_h__4_1121_);
v_pre_1131_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_pre_1131_);
v_i_1132_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_i_1132_);
lean_dec_ref_known(v_x_1116_, 2);
v_pre_1133_ = lean_ctor_get(v_x_1117_, 0);
lean_inc(v_pre_1133_);
v_i_1134_ = lean_ctor_get(v_x_1117_, 1);
lean_inc(v_i_1134_);
lean_dec_ref_known(v_x_1117_, 2);
v___x_1135_ = lean_apply_4(v_h__3_1120_, v_pre_1131_, v_i_1132_, v_pre_1133_, v_i_1134_);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; 
lean_dec(v_h__3_1120_);
v___x_1136_ = lean_apply_5(v_h__4_1121_, v_x_1116_, v_x_1117_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Name_instDecidableEq(lean_object* v_a_1137_, lean_object* v_b_1138_){
_start:
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_name_eq(v_a_1137_, v_b_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object* v_a_1140_, lean_object* v_b_1141_){
_start:
{
uint8_t v_res_1142_; lean_object* v_r_1143_; 
v_res_1142_ = l_Lean_Name_instDecidableEq(v_a_1140_, v_b_1141_);
lean_dec(v_b_1141_);
lean_dec(v_a_1140_);
v_r_1143_ = lean_box(v_res_1142_);
return v_r_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object* v_g_1144_){
_start:
{
lean_object* v_namePrefix_1145_; lean_object* v_idx_1146_; lean_object* v___x_1147_; 
v_namePrefix_1145_ = lean_ctor_get(v_g_1144_, 0);
lean_inc(v_namePrefix_1145_);
v_idx_1146_ = lean_ctor_get(v_g_1144_, 1);
lean_inc(v_idx_1146_);
lean_dec_ref(v_g_1144_);
v___x_1147_ = l_Lean_Name_num___override(v_namePrefix_1145_, v_idx_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object* v_g_1148_){
_start:
{
lean_object* v_namePrefix_1149_; lean_object* v_idx_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1159_; 
v_namePrefix_1149_ = lean_ctor_get(v_g_1148_, 0);
v_idx_1150_ = lean_ctor_get(v_g_1148_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_g_1148_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1152_ = v_g_1148_;
v_isShared_1153_ = v_isSharedCheck_1159_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_idx_1150_);
lean_inc(v_namePrefix_1149_);
lean_dec(v_g_1148_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1159_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1154_ = lean_unsigned_to_nat(1u);
v___x_1155_ = lean_nat_add(v_idx_1150_, v___x_1154_);
lean_dec(v_idx_1150_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v___x_1155_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_namePrefix_1149_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object* v_g_1160_){
_start:
{
lean_object* v_namePrefix_1161_; lean_object* v_idx_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1174_; 
v_namePrefix_1161_ = lean_ctor_get(v_g_1160_, 0);
v_idx_1162_ = lean_ctor_get(v_g_1160_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_g_1160_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1164_ = v_g_1160_;
v_isShared_1165_ = v_isSharedCheck_1174_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_idx_1162_);
lean_inc(v_namePrefix_1161_);
lean_dec(v_g_1160_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1174_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
lean_inc(v_idx_1162_);
lean_inc(v_namePrefix_1161_);
v___x_1166_ = l_Lean_Name_num___override(v_namePrefix_1161_, v_idx_1162_);
v___x_1167_ = lean_unsigned_to_nat(1u);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1167_);
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = lean_nat_add(v_idx_1162_, v___x_1167_);
lean_dec(v_idx_1162_);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_namePrefix_1161_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1169_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object* v_toPure_1175_, lean_object* v_r_1176_, lean_object* v_____r_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_apply_2(v_toPure_1175_, lean_box(0), v_r_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object* v_toPure_1179_, lean_object* v_setNGen_1180_, lean_object* v_toBind_1181_, lean_object* v_ngen_1182_){
_start:
{
lean_object* v_namePrefix_1183_; lean_object* v_idx_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1197_; 
v_namePrefix_1183_ = lean_ctor_get(v_ngen_1182_, 0);
v_idx_1184_ = lean_ctor_get(v_ngen_1182_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_ngen_1182_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1186_ = v_ngen_1182_;
v_isShared_1187_ = v_isSharedCheck_1197_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_idx_1184_);
lean_inc(v_namePrefix_1183_);
lean_dec(v_ngen_1182_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1197_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_r_1188_; lean_object* v___f_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
lean_inc(v_idx_1184_);
lean_inc(v_namePrefix_1183_);
v_r_1188_ = l_Lean_Name_num___override(v_namePrefix_1183_, v_idx_1184_);
v___f_1189_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1189_, 0, v_toPure_1179_);
lean_closure_set(v___f_1189_, 1, v_r_1188_);
v___x_1190_ = lean_unsigned_to_nat(1u);
v___x_1191_ = lean_nat_add(v_idx_1184_, v___x_1190_);
lean_dec(v_idx_1184_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v___x_1191_);
v___x_1193_ = v___x_1186_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_namePrefix_1183_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_apply_1(v_setNGen_1180_, v___x_1193_);
v___x_1195_ = lean_apply_4(v_toBind_1181_, lean_box(0), lean_box(0), v___x_1194_, v___f_1189_);
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object* v_inst_1198_, lean_object* v_inst_1199_){
_start:
{
lean_object* v_toApplicative_1200_; lean_object* v_toBind_1201_; lean_object* v_getNGen_1202_; lean_object* v_setNGen_1203_; lean_object* v_toPure_1204_; lean_object* v___f_1205_; lean_object* v___x_1206_; 
v_toApplicative_1200_ = lean_ctor_get(v_inst_1198_, 0);
lean_inc_ref(v_toApplicative_1200_);
v_toBind_1201_ = lean_ctor_get(v_inst_1198_, 1);
lean_inc_n(v_toBind_1201_, 2);
lean_dec_ref(v_inst_1198_);
v_getNGen_1202_ = lean_ctor_get(v_inst_1199_, 0);
lean_inc(v_getNGen_1202_);
v_setNGen_1203_ = lean_ctor_get(v_inst_1199_, 1);
lean_inc(v_setNGen_1203_);
lean_dec_ref(v_inst_1199_);
v_toPure_1204_ = lean_ctor_get(v_toApplicative_1200_, 1);
lean_inc(v_toPure_1204_);
lean_dec_ref(v_toApplicative_1200_);
v___f_1205_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1205_, 0, v_toPure_1204_);
lean_closure_set(v___f_1205_, 1, v_setNGen_1203_);
lean_closure_set(v___f_1205_, 2, v_toBind_1201_);
v___x_1206_ = lean_apply_4(v_toBind_1201_, lean_box(0), lean_box(0), v_getNGen_1202_, v___f_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object* v_m_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_mkFreshId___redArg(v_inst_1208_, v_inst_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object* v_setNGen_1211_, lean_object* v_inst_1212_, lean_object* v_ngen_1213_){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_apply_1(v_setNGen_1211_, v_ngen_1213_);
v___x_1215_ = lean_apply_2(v_inst_1212_, lean_box(0), v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object* v_inst_1216_, lean_object* v_inst_1217_){
_start:
{
lean_object* v_getNGen_1218_; lean_object* v_setNGen_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1228_; 
v_getNGen_1218_ = lean_ctor_get(v_inst_1217_, 0);
v_setNGen_1219_ = lean_ctor_get(v_inst_1217_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_inst_1217_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1221_ = v_inst_1217_;
v_isShared_1222_ = v_isSharedCheck_1228_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_setNGen_1219_);
lean_inc(v_getNGen_1218_);
lean_dec(v_inst_1217_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1228_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___f_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
lean_inc(v_inst_1216_);
v___f_1223_ = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1223_, 0, v_setNGen_1219_);
lean_closure_set(v___f_1223_, 1, v_inst_1216_);
v___x_1224_ = lean_apply_2(v_inst_1216_, lean_box(0), v_getNGen_1218_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v___f_1223_);
lean_ctor_set(v___x_1221_, 0, v___x_1224_);
v___x_1226_ = v___x_1221_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v___f_1223_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object* v_m_1229_, lean_object* v_n_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_monadNameGeneratorLift___redArg(v_inst_1231_, v_inst_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1234_, lean_object* v_x_1235_, lean_object* v_x_1236_){
_start:
{
if (lean_obj_tag(v_x_1236_) == 0)
{
lean_dec(v_x_1234_);
return v_x_1235_;
}
else
{
lean_object* v_head_1237_; lean_object* v_tail_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1249_; 
v_head_1237_ = lean_ctor_get(v_x_1236_, 0);
v_tail_1238_ = lean_ctor_get(v_x_1236_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_x_1236_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1240_ = v_x_1236_;
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_tail_1238_);
lean_inc(v_head_1237_);
lean_dec(v_x_1236_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
lean_inc(v_x_1234_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 5);
lean_ctor_set(v___x_1240_, 1, v_x_1234_);
lean_ctor_set(v___x_1240_, 0, v_x_1235_);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_x_1235_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_x_1234_);
v___x_1243_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = l_String_quote(v_head_1237_);
v___x_1245_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
v___x_1246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1243_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v_x_1235_ = v___x_1246_;
v_x_1236_ = v_tail_1238_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object* v_x_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
lean_dec(v_x_1250_);
return v_x_1251_;
}
else
{
lean_object* v_head_1253_; lean_object* v_tail_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1265_; 
v_head_1253_ = lean_ctor_get(v_x_1252_, 0);
v_tail_1254_ = lean_ctor_get(v_x_1252_, 1);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_x_1252_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1256_ = v_x_1252_;
v_isShared_1257_ = v_isSharedCheck_1265_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_tail_1254_);
lean_inc(v_head_1253_);
lean_dec(v_x_1252_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1265_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
lean_inc(v_x_1250_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set_tag(v___x_1256_, 5);
lean_ctor_set(v___x_1256_, 1, v_x_1250_);
lean_ctor_set(v___x_1256_, 0, v_x_1251_);
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_x_1251_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_x_1250_);
v___x_1259_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1260_ = l_String_quote(v_head_1253_);
v___x_1261_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1259_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(v_x_1250_, v___x_1262_, v_tail_1254_);
return v___x_1263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = l_String_quote(v___y_1266_);
v___x_1268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
if (lean_obj_tag(v_x_1269_) == 0)
{
lean_object* v___x_1271_; 
lean_dec(v_x_1270_);
v___x_1271_ = lean_box(0);
return v___x_1271_;
}
else
{
lean_object* v_tail_1272_; 
v_tail_1272_ = lean_ctor_get(v_x_1269_, 1);
if (lean_obj_tag(v_tail_1272_) == 0)
{
lean_object* v_head_1273_; lean_object* v___x_1274_; 
lean_dec(v_x_1270_);
v_head_1273_ = lean_ctor_get(v_x_1269_, 0);
lean_inc(v_head_1273_);
lean_dec_ref_known(v_x_1269_, 2);
v___x_1274_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1273_);
return v___x_1274_;
}
else
{
lean_object* v_head_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_inc(v_tail_1272_);
v_head_1275_ = lean_ctor_get(v_x_1269_, 0);
lean_inc(v_head_1275_);
lean_dec_ref_known(v_x_1269_, 2);
v___x_1276_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1275_);
v___x_1277_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(v_x_1270_, v___x_1276_, v_tail_1272_);
return v___x_1277_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2));
v___x_1290_ = lean_string_length(v___x_1289_);
return v___x_1290_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7);
v___x_1292_ = lean_nat_to_int(v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object* v_a_1297_){
_start:
{
if (lean_obj_tag(v_a_1297_) == 0)
{
lean_object* v___x_1298_; 
v___x_1298_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1298_;
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1299_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1300_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(v_a_1297_, v___x_1299_);
v___x_1301_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1302_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set(v___x_1303_, 1, v___x_1300_);
v___x_1304_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1303_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1301_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = l_Std_Format_fill(v___x_1306_);
return v___x_1307_;
}
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_unsigned_to_nat(2u);
v___x_1315_ = lean_nat_to_int(v___x_1314_);
return v___x_1315_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_unsigned_to_nat(1u);
v___x_1317_ = lean_nat_to_int(v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object* v_x_1324_, lean_object* v_prec_1325_){
_start:
{
if (lean_obj_tag(v_x_1324_) == 0)
{
lean_object* v_ns_1326_; lean_object* v___y_1328_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v_ns_1326_ = lean_ctor_get(v_x_1324_, 0);
lean_inc(v_ns_1326_);
lean_dec_ref_known(v_x_1324_, 1);
v___x_1337_ = lean_unsigned_to_nat(1024u);
v___x_1338_ = lean_nat_dec_le(v___x_1337_, v_prec_1325_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1328_ = v___x_1339_;
goto v___jp_1327_;
}
else
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1328_ = v___x_1340_;
goto v___jp_1327_;
}
v___jp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1329_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__2));
v___x_1330_ = lean_unsigned_to_nat(1024u);
v___x_1331_ = l_Lean_Name_reprPrec(v_ns_1326_, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1329_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
lean_inc(v___y_1328_);
v___x_1333_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___y_1328_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = 0;
v___x_1335_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*1, v___x_1334_);
v___x_1336_ = l_Repr_addAppParen(v___x_1335_, v_prec_1325_);
return v___x_1336_;
}
}
else
{
lean_object* v_n_1341_; lean_object* v_fields_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1366_; 
v_n_1341_ = lean_ctor_get(v_x_1324_, 0);
v_fields_1342_ = lean_ctor_get(v_x_1324_, 1);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_x_1324_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1344_ = v_x_1324_;
v_isShared_1345_ = v_isSharedCheck_1366_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_fields_1342_);
lean_inc(v_n_1341_);
lean_dec(v_x_1324_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1366_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___y_1347_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = lean_unsigned_to_nat(1024u);
v___x_1363_ = lean_nat_dec_le(v___x_1362_, v_prec_1325_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1347_ = v___x_1364_;
goto v___jp_1346_;
}
else
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1347_ = v___x_1365_;
goto v___jp_1346_;
}
v___jp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1348_ = lean_box(1);
v___x_1349_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__7));
v___x_1350_ = lean_unsigned_to_nat(1024u);
v___x_1351_ = l_Lean_Name_reprPrec(v_n_1341_, v___x_1350_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 5);
lean_ctor_set(v___x_1344_, 1, v___x_1351_);
lean_ctor_set(v___x_1344_, 0, v___x_1349_);
v___x_1353_ = v___x_1344_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1354_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v___x_1348_);
v___x_1355_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_fields_1342_);
v___x_1356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
lean_inc(v___y_1347_);
v___x_1357_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___y_1347_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = 0;
v___x_1359_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*1, v___x_1358_);
v___x_1360_ = l_Repr_addAppParen(v___x_1359_, v_prec_1325_);
return v___x_1360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object* v_x_1367_, lean_object* v_prec_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Syntax_instReprPreresolved_repr(v_x_1367_, v_prec_1368_);
lean_dec(v_prec_1368_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object* v_a_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_nat_to_int(v_a_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object* v_a_1372_, lean_object* v_n_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_a_1372_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object* v_a_1375_, lean_object* v_n_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(v_a_1375_, v_n_1376_);
lean_dec(v_n_1376_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = l_Lean_Syntax_instReprPreresolved_repr(v___y_1380_, v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_){
_start:
{
if (lean_obj_tag(v_x_1385_) == 0)
{
lean_dec(v_x_1383_);
return v_x_1384_;
}
else
{
lean_object* v_head_1386_; lean_object* v_tail_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1398_; 
v_head_1386_ = lean_ctor_get(v_x_1385_, 0);
v_tail_1387_ = lean_ctor_get(v_x_1385_, 1);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_x_1385_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1389_ = v_x_1385_;
v_isShared_1390_ = v_isSharedCheck_1398_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_tail_1387_);
lean_inc(v_head_1386_);
lean_dec(v_x_1385_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1398_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
lean_inc(v_x_1383_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set_tag(v___x_1389_, 5);
lean_ctor_set(v___x_1389_, 1, v_x_1383_);
lean_ctor_set(v___x_1389_, 0, v_x_1384_);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_x_1384_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_x_1383_);
v___x_1392_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1386_, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1392_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v_x_1384_ = v___x_1395_;
v_x_1385_ = v_tail_1387_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object* v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
if (lean_obj_tag(v_x_1401_) == 0)
{
lean_dec(v_x_1399_);
return v_x_1400_;
}
else
{
lean_object* v_head_1402_; lean_object* v_tail_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1414_; 
v_head_1402_ = lean_ctor_get(v_x_1401_, 0);
v_tail_1403_ = lean_ctor_get(v_x_1401_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_x_1401_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1405_ = v_x_1401_;
v_isShared_1406_ = v_isSharedCheck_1414_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_tail_1403_);
lean_inc(v_head_1402_);
lean_dec(v_x_1401_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1414_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
lean_inc(v_x_1399_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 5);
lean_ctor_set(v___x_1405_, 1, v_x_1399_);
lean_ctor_set(v___x_1405_, 0, v_x_1400_);
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_x_1400_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_x_1399_);
v___x_1408_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1402_, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1408_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(v_x_1399_, v___x_1411_, v_tail_1403_);
return v___x_1412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object* v_x_1415_, lean_object* v_x_1416_){
_start:
{
if (lean_obj_tag(v_x_1415_) == 0)
{
lean_object* v___x_1417_; 
lean_dec(v_x_1416_);
v___x_1417_ = lean_box(0);
return v___x_1417_;
}
else
{
lean_object* v_tail_1418_; 
v_tail_1418_ = lean_ctor_get(v_x_1415_, 1);
if (lean_obj_tag(v_tail_1418_) == 0)
{
lean_object* v_head_1419_; lean_object* v___x_1420_; 
lean_dec(v_x_1416_);
v_head_1419_ = lean_ctor_get(v_x_1415_, 0);
lean_inc(v_head_1419_);
lean_dec_ref_known(v_x_1415_, 2);
v___x_1420_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1419_);
return v___x_1420_;
}
else
{
lean_object* v_head_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_inc(v_tail_1418_);
v_head_1421_ = lean_ctor_get(v_x_1415_, 0);
lean_inc(v_head_1421_);
lean_dec_ref_known(v_x_1415_, 2);
v___x_1422_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1421_);
v___x_1423_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(v_x_1416_, v___x_1422_, v_tail_1418_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object* v_a_1424_){
_start:
{
if (lean_obj_tag(v_a_1424_) == 0)
{
lean_object* v___x_1425_; 
v___x_1425_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; 
v___x_1426_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1427_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(v_a_1424_, v___x_1426_);
v___x_1428_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1429_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1427_);
v___x_1431_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1428_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = 0;
v___x_1435_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set_uint8(v___x_1435_, sizeof(void*)*1, v___x_1434_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
if (lean_obj_tag(v_x_1447_) == 0)
{
lean_dec(v_x_1445_);
return v_x_1446_;
}
else
{
lean_object* v_head_1448_; lean_object* v_tail_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1460_; 
v_head_1448_ = lean_ctor_get(v_x_1447_, 0);
v_tail_1449_ = lean_ctor_get(v_x_1447_, 1);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_x_1447_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1451_ = v_x_1447_;
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_tail_1449_);
lean_inc(v_head_1448_);
lean_dec(v_x_1447_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
lean_inc(v_x_1445_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set_tag(v___x_1451_, 5);
lean_ctor_set(v___x_1451_, 1, v_x_1445_);
lean_ctor_set(v___x_1451_, 0, v_x_1446_);
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_x_1446_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_x_1445_);
v___x_1454_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = l_Lean_Syntax_instRepr_repr(v_head_1448_, v___x_1455_);
v___x_1457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1454_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v_x_1446_ = v___x_1457_;
v_x_1447_ = v_tail_1449_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_){
_start:
{
if (lean_obj_tag(v_x_1463_) == 0)
{
lean_dec(v_x_1461_);
return v_x_1462_;
}
else
{
lean_object* v_head_1464_; lean_object* v_tail_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1476_; 
v_head_1464_ = lean_ctor_get(v_x_1463_, 0);
v_tail_1465_ = lean_ctor_get(v_x_1463_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_x_1463_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1467_ = v_x_1463_;
v_isShared_1468_ = v_isSharedCheck_1476_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_tail_1465_);
lean_inc(v_head_1464_);
lean_dec(v_x_1463_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1476_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
lean_inc(v_x_1461_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set_tag(v___x_1467_, 5);
lean_ctor_set(v___x_1467_, 1, v_x_1461_);
lean_ctor_set(v___x_1467_, 0, v_x_1462_);
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_x_1462_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_x_1461_);
v___x_1470_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = l_Lean_Syntax_instRepr_repr(v_head_1464_, v___x_1471_);
v___x_1473_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1470_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(v_x_1461_, v___x_1473_, v_tail_1465_);
return v___x_1474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object* v_x_1477_, lean_object* v_x_1478_){
_start:
{
if (lean_obj_tag(v_x_1477_) == 0)
{
lean_object* v___x_1479_; 
lean_dec(v_x_1478_);
v___x_1479_ = lean_box(0);
return v___x_1479_;
}
else
{
lean_object* v_tail_1480_; 
v_tail_1480_ = lean_ctor_get(v_x_1477_, 1);
if (lean_obj_tag(v_tail_1480_) == 0)
{
lean_object* v_head_1481_; lean_object* v___x_1482_; 
lean_dec(v_x_1478_);
v_head_1481_ = lean_ctor_get(v_x_1477_, 0);
lean_inc(v_head_1481_);
lean_dec_ref_known(v_x_1477_, 2);
v___x_1482_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1481_);
return v___x_1482_;
}
else
{
lean_object* v_head_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_inc(v_tail_1480_);
v_head_1483_ = lean_ctor_get(v_x_1477_, 0);
lean_inc(v_head_1483_);
lean_dec_ref_known(v_x_1477_, 2);
v___x_1484_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1483_);
v___x_1485_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(v_x_1478_, v___x_1484_, v_tail_1480_);
return v___x_1485_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0));
v___x_1488_ = lean_string_length(v___x_1487_);
return v___x_1488_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1);
v___x_1490_ = lean_nat_to_int(v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object* v_xs_1496_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1497_ = lean_array_get_size(v_xs_1496_);
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = lean_nat_dec_eq(v___x_1497_, v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1500_ = lean_array_to_list(v_xs_1496_);
v___x_1501_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1502_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(v___x_1500_, v___x_1501_);
v___x_1503_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2);
v___x_1504_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3));
v___x_1505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v___x_1502_);
v___x_1506_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1503_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = l_Std_Format_fill(v___x_1508_);
return v___x_1509_;
}
else
{
lean_object* v___x_1510_; 
lean_dec_ref(v_xs_1496_);
v___x_1510_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5));
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object* v_x_1524_, lean_object* v_prec_1525_){
_start:
{
lean_object* v___y_1527_; 
switch(lean_obj_tag(v_x_1524_))
{
case 0:
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = lean_unsigned_to_nat(1024u);
v___x_1534_ = lean_nat_dec_le(v___x_1533_, v_prec_1525_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1527_ = v___x_1535_;
goto v___jp_1526_;
}
else
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1527_ = v___x_1536_;
goto v___jp_1526_;
}
}
case 1:
{
lean_object* v_info_1537_; lean_object* v_kind_1538_; lean_object* v_args_1539_; lean_object* v___y_1541_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v_info_1537_ = lean_ctor_get(v_x_1524_, 0);
lean_inc(v_info_1537_);
v_kind_1538_ = lean_ctor_get(v_x_1524_, 1);
lean_inc(v_kind_1538_);
v_args_1539_ = lean_ctor_get(v_x_1524_, 2);
lean_inc_ref(v_args_1539_);
lean_dec_ref_known(v_x_1524_, 3);
v___x_1557_ = lean_unsigned_to_nat(1024u);
v___x_1558_ = lean_nat_dec_le(v___x_1557_, v_prec_1525_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1541_ = v___x_1559_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1541_ = v___x_1560_;
goto v___jp_1540_;
}
v___jp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1542_ = lean_box(1);
v___x_1543_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__4));
v___x_1544_ = lean_unsigned_to_nat(1024u);
v___x_1545_ = l_instReprSourceInfo_repr(v_info_1537_, v___x_1544_);
v___x_1546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1543_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v___x_1542_);
v___x_1548_ = l_Lean_Name_reprPrec(v_kind_1538_, v___x_1544_);
v___x_1549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v___x_1542_);
v___x_1551_ = l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(v_args_1539_);
v___x_1552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
lean_inc(v___y_1541_);
v___x_1553_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___y_1541_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = 0;
v___x_1555_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*1, v___x_1554_);
v___x_1556_ = l_Repr_addAppParen(v___x_1555_, v_prec_1525_);
return v___x_1556_;
}
}
case 2:
{
lean_object* v_info_1561_; lean_object* v_val_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1587_; 
v_info_1561_ = lean_ctor_get(v_x_1524_, 0);
v_val_1562_ = lean_ctor_get(v_x_1524_, 1);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_x_1524_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1564_ = v_x_1524_;
v_isShared_1565_ = v_isSharedCheck_1587_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_val_1562_);
lean_inc(v_info_1561_);
lean_dec(v_x_1524_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1587_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___y_1567_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = lean_unsigned_to_nat(1024u);
v___x_1584_ = lean_nat_dec_le(v___x_1583_, v_prec_1525_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1567_ = v___x_1585_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1567_ = v___x_1586_;
goto v___jp_1566_;
}
v___jp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1568_ = lean_box(1);
v___x_1569_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__7));
v___x_1570_ = lean_unsigned_to_nat(1024u);
v___x_1571_ = l_instReprSourceInfo_repr(v_info_1561_, v___x_1570_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set_tag(v___x_1564_, 5);
lean_ctor_set(v___x_1564_, 1, v___x_1571_);
lean_ctor_set(v___x_1564_, 0, v___x_1569_);
v___x_1573_ = v___x_1564_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v___x_1568_);
v___x_1575_ = l_String_quote(v_val_1562_);
v___x_1576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1574_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
lean_inc(v___y_1567_);
v___x_1578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___y_1567_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = 0;
v___x_1580_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*1, v___x_1579_);
v___x_1581_ = l_Repr_addAppParen(v___x_1580_, v_prec_1525_);
return v___x_1581_;
}
}
}
}
default: 
{
lean_object* v_info_1588_; lean_object* v_rawVal_1589_; lean_object* v_val_1590_; lean_object* v_preresolved_1591_; lean_object* v___y_1593_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v_info_1588_ = lean_ctor_get(v_x_1524_, 0);
lean_inc(v_info_1588_);
v_rawVal_1589_ = lean_ctor_get(v_x_1524_, 1);
lean_inc_ref(v_rawVal_1589_);
v_val_1590_ = lean_ctor_get(v_x_1524_, 2);
lean_inc(v_val_1590_);
v_preresolved_1591_ = lean_ctor_get(v_x_1524_, 3);
lean_inc(v_preresolved_1591_);
lean_dec_ref_known(v_x_1524_, 4);
v___x_1616_ = lean_unsigned_to_nat(1024u);
v___x_1617_ = lean_nat_dec_le(v___x_1616_, v_prec_1525_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1593_ = v___x_1618_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1593_ = v___x_1619_;
goto v___jp_1592_;
}
v___jp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1594_ = lean_box(1);
v___x_1595_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__10));
v___x_1596_ = lean_unsigned_to_nat(1024u);
v___x_1597_ = l_instReprSourceInfo_repr(v_info_1588_, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1595_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v___x_1594_);
v___x_1600_ = lean_substring_tostring(v_rawVal_1589_);
v___x_1601_ = l_String_quote(v___x_1600_);
v___x_1602_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__11));
v___x_1603_ = lean_string_append(v___x_1601_, v___x_1602_);
v___x_1604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
v___x_1605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1599_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v___x_1594_);
v___x_1607_ = l_Lean_Name_reprPrec(v_val_1590_, v___x_1596_);
v___x_1608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
lean_ctor_set(v___x_1609_, 1, v___x_1594_);
v___x_1610_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_preresolved_1591_);
v___x_1611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
lean_inc(v___y_1593_);
v___x_1612_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___y_1593_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = 0;
v___x_1614_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set_uint8(v___x_1614_, sizeof(void*)*1, v___x_1613_);
v___x_1615_ = l_Repr_addAppParen(v___x_1614_, v_prec_1525_);
return v___x_1615_;
}
}
}
v___jp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1528_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__1));
lean_inc(v___y_1527_);
v___x_1529_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___y_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = 0;
v___x_1531_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set_uint8(v___x_1531_, sizeof(void*)*1, v___x_1530_);
v___x_1532_ = l_Repr_addAppParen(v___x_1531_, v_prec_1525_);
return v___x_1532_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = l_Lean_Syntax_instRepr_repr(v___y_1620_, v___x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object* v_x_1623_, lean_object* v_prec_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Syntax_instRepr_repr(v_x_1623_, v_prec_1624_);
lean_dec(v_prec_1624_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object* v_a_1626_, lean_object* v_n_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_a_1626_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object* v_a_1629_, lean_object* v_n_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(v_a_1629_, v_n_1630_);
lean_dec(v_n_1630_);
return v_res_1631_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_unsigned_to_nat(7u);
v___x_1648_ = lean_nat_to_int(v___x_1647_);
return v___x_1648_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0));
v___x_1651_ = lean_string_length(v___x_1650_);
return v___x_1651_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9);
v___x_1653_ = lean_nat_to_int(v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object* v_x_1658_){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1659_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6));
v___x_1660_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = l_Lean_Syntax_instRepr_repr(v_x_1658_, v___x_1661_);
v___x_1663_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1660_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = 0;
v___x_1665_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set_uint8(v___x_1665_, sizeof(void*)*1, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1659_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_1668_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_1669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
lean_ctor_set(v___x_1669_, 1, v___x_1666_);
v___x_1670_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_1671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1667_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set_uint8(v___x_1673_, sizeof(void*)*1, v___x_1664_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object* v_ks_1674_, lean_object* v_x_1675_, lean_object* v_prec_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_x_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object* v_ks_1678_, lean_object* v_x_1679_, lean_object* v_prec_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_Syntax_instReprTSyntax_repr(v_ks_1678_, v_x_1679_, v_prec_1680_);
lean_dec(v_prec_1680_);
lean_dec(v_ks_1678_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object* v_ks_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_alloc_closure((void*)(l_Lean_Syntax_instReprTSyntax_repr___boxed), 3, 1);
lean_closure_set(v___x_1683_, 0, v_ks_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_stx_1684_){
_start:
{
lean_inc(v_stx_1684_);
return v_stx_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0___boxed(lean_object* v_stx_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(v_stx_1685_);
lean_dec(v_stx_1685_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg(){
_start:
{
lean_object* v___f_1689_; 
v___f_1689_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___boxed(lean_object* v___dummy_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg();
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object* v_k_1692_, lean_object* v_ks_1693_){
_start:
{
lean_object* v___f_1694_; 
v___f_1694_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object* v_k_1695_, lean_object* v_ks_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(v_k_1695_, v_ks_1696_);
lean_dec(v_ks_1696_);
lean_dec(v_k_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg(){
_start:
{
lean_object* v___f_1699_; 
v___f_1699_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg___boxed(lean_object* v___dummy_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg();
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object* v_ks_1702_, lean_object* v_k_x27_1703_){
_start:
{
lean_object* v___f_1704_; 
v___f_1704_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object* v_ks_1705_, lean_object* v_k_x27_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind(v_ks_1705_, v_k_x27_1706_);
lean_dec(v_k_x27_1706_);
lean_dec(v_ks_1705_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object* v_s_1708_){
_start:
{
lean_inc(v_s_1708_);
return v_s_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object* v_s_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_TSyntax_instCoeIdentTerm___lam__0(v_s_1709_);
lean_dec(v_s_1709_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object* v_info_1713_, lean_object* v_ss_1714_, lean_object* v_n_1715_, lean_object* v_res_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1717_, 0, v_info_1713_);
lean_ctor_set(v___x_1717_, 1, v_ss_1714_);
lean_ctor_set(v___x_1717_, 2, v_n_1715_);
lean_ctor_set(v___x_1717_, 3, v_res_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg(){
_start:
{
lean_object* v___f_1727_; 
v___f_1727_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg___boxed(lean_object* v___dummy_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg();
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object* v_k_1730_){
_start:
{
lean_object* v___f_1731_; 
v___f_1731_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object* v_k_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_TSyntax_Compat_instCoeTailSyntax(v_k_1732_);
lean_dec(v_k_1732_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object* v_k_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_alloc_closure((void*)(l_Lean_TSyntaxArray_mkImpl___boxed), 2, 1);
lean_closure_set(v___x_1735_, 0, v_k_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object* v_x_1736_, lean_object* v_x_1737_){
_start:
{
if (lean_obj_tag(v_x_1736_) == 0)
{
if (lean_obj_tag(v_x_1737_) == 0)
{
uint8_t v___x_1738_; 
v___x_1738_ = 1;
return v___x_1738_;
}
else
{
uint8_t v___x_1739_; 
v___x_1739_ = 0;
return v___x_1739_;
}
}
else
{
if (lean_obj_tag(v_x_1737_) == 0)
{
uint8_t v___x_1740_; 
v___x_1740_ = 0;
return v___x_1740_;
}
else
{
lean_object* v_head_1741_; lean_object* v_tail_1742_; lean_object* v_head_1743_; lean_object* v_tail_1744_; uint8_t v___x_1745_; 
v_head_1741_ = lean_ctor_get(v_x_1736_, 0);
v_tail_1742_ = lean_ctor_get(v_x_1736_, 1);
v_head_1743_ = lean_ctor_get(v_x_1737_, 0);
v_tail_1744_ = lean_ctor_get(v_x_1737_, 1);
v___x_1745_ = lean_string_dec_eq(v_head_1741_, v_head_1743_);
if (v___x_1745_ == 0)
{
return v___x_1745_;
}
else
{
v_x_1736_ = v_tail_1742_;
v_x_1737_ = v_tail_1744_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object* v_x_1747_, lean_object* v_x_1748_){
_start:
{
uint8_t v_res_1749_; lean_object* v_r_1750_; 
v_res_1749_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_x_1747_, v_x_1748_);
lean_dec(v_x_1748_);
lean_dec(v_x_1747_);
v_r_1750_ = lean_box(v_res_1749_);
return v_r_1750_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
if (lean_obj_tag(v_x_1751_) == 0)
{
if (lean_obj_tag(v_x_1752_) == 0)
{
lean_object* v_ns_1753_; lean_object* v_ns_1754_; uint8_t v___x_1755_; 
v_ns_1753_ = lean_ctor_get(v_x_1751_, 0);
v_ns_1754_ = lean_ctor_get(v_x_1752_, 0);
v___x_1755_ = lean_name_eq(v_ns_1753_, v_ns_1754_);
return v___x_1755_;
}
else
{
uint8_t v___x_1756_; 
v___x_1756_ = 0;
return v___x_1756_;
}
}
else
{
if (lean_obj_tag(v_x_1752_) == 1)
{
lean_object* v_n_1757_; lean_object* v_fields_1758_; lean_object* v_n_1759_; lean_object* v_fields_1760_; uint8_t v___x_1761_; 
v_n_1757_ = lean_ctor_get(v_x_1751_, 0);
v_fields_1758_ = lean_ctor_get(v_x_1751_, 1);
v_n_1759_ = lean_ctor_get(v_x_1752_, 0);
v_fields_1760_ = lean_ctor_get(v_x_1752_, 1);
v___x_1761_ = lean_name_eq(v_n_1757_, v_n_1759_);
if (v___x_1761_ == 0)
{
return v___x_1761_;
}
else
{
uint8_t v___x_1762_; 
v___x_1762_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_fields_1758_, v_fields_1760_);
return v___x_1762_;
}
}
else
{
uint8_t v___x_1763_; 
v___x_1763_ = 0;
return v___x_1763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
uint8_t v_res_1766_; lean_object* v_r_1767_; 
v_res_1766_ = l_Lean_Syntax_instBEqPreresolved_beq(v_x_1764_, v_x_1765_);
lean_dec_ref(v_x_1765_);
lean_dec_ref(v_x_1764_);
v_r_1767_ = lean_box(v_res_1766_);
return v_r_1767_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object* v_x_1770_, lean_object* v_x_1771_){
_start:
{
if (lean_obj_tag(v_x_1770_) == 0)
{
if (lean_obj_tag(v_x_1771_) == 0)
{
uint8_t v___x_1772_; 
v___x_1772_ = 1;
return v___x_1772_;
}
else
{
uint8_t v___x_1773_; 
v___x_1773_ = 0;
return v___x_1773_;
}
}
else
{
if (lean_obj_tag(v_x_1771_) == 0)
{
uint8_t v___x_1774_; 
v___x_1774_ = 0;
return v___x_1774_;
}
else
{
lean_object* v_head_1775_; lean_object* v_tail_1776_; lean_object* v_head_1777_; lean_object* v_tail_1778_; uint8_t v___x_1779_; 
v_head_1775_ = lean_ctor_get(v_x_1770_, 0);
v_tail_1776_ = lean_ctor_get(v_x_1770_, 1);
v_head_1777_ = lean_ctor_get(v_x_1771_, 0);
v_tail_1778_ = lean_ctor_get(v_x_1771_, 1);
v___x_1779_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_1775_, v_head_1777_);
if (v___x_1779_ == 0)
{
return v___x_1779_;
}
else
{
v_x_1770_ = v_tail_1776_;
v_x_1771_ = v_tail_1778_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object* v_x_1781_, lean_object* v_x_1782_){
_start:
{
uint8_t v_res_1783_; lean_object* v_r_1784_; 
v_res_1783_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_x_1781_, v_x_1782_);
lean_dec(v_x_1782_);
lean_dec(v_x_1781_);
v_r_1784_ = lean_box(v_res_1783_);
return v_r_1784_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structEq(lean_object* v_x_1785_, lean_object* v_x_1786_){
_start:
{
switch(lean_obj_tag(v_x_1785_))
{
case 0:
{
if (lean_obj_tag(v_x_1786_) == 0)
{
uint8_t v___x_1787_; 
v___x_1787_ = 1;
return v___x_1787_;
}
else
{
uint8_t v___x_1788_; 
v___x_1788_ = 0;
return v___x_1788_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1786_) == 1)
{
lean_object* v_kind_1789_; lean_object* v_args_1790_; lean_object* v_kind_1791_; lean_object* v_args_1792_; uint8_t v___x_1793_; 
v_kind_1789_ = lean_ctor_get(v_x_1785_, 1);
v_args_1790_ = lean_ctor_get(v_x_1785_, 2);
v_kind_1791_ = lean_ctor_get(v_x_1786_, 1);
v_args_1792_ = lean_ctor_get(v_x_1786_, 2);
v___x_1793_ = lean_name_eq(v_kind_1789_, v_kind_1791_);
if (v___x_1793_ == 0)
{
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1794_ = lean_array_get_size(v_args_1790_);
v___x_1795_ = lean_array_get_size(v_args_1792_);
v___x_1796_ = lean_nat_dec_eq(v___x_1794_, v___x_1795_);
if (v___x_1796_ == 0)
{
return v___x_1796_;
}
else
{
uint8_t v___x_1797_; 
v___x_1797_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_args_1790_, v_args_1792_, v___x_1794_);
return v___x_1797_;
}
}
}
else
{
uint8_t v___x_1798_; 
v___x_1798_ = 0;
return v___x_1798_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1786_) == 2)
{
lean_object* v_val_1799_; lean_object* v_val_1800_; uint8_t v___x_1801_; 
v_val_1799_ = lean_ctor_get(v_x_1785_, 1);
v_val_1800_ = lean_ctor_get(v_x_1786_, 1);
v___x_1801_ = lean_string_dec_eq(v_val_1799_, v_val_1800_);
return v___x_1801_;
}
else
{
uint8_t v___x_1802_; 
v___x_1802_ = 0;
return v___x_1802_;
}
}
default: 
{
if (lean_obj_tag(v_x_1786_) == 3)
{
lean_object* v_rawVal_1803_; lean_object* v_val_1804_; lean_object* v_preresolved_1805_; lean_object* v_rawVal_1806_; lean_object* v_val_1807_; lean_object* v_preresolved_1808_; uint8_t v___y_1810_; uint8_t v___x_1812_; 
v_rawVal_1803_ = lean_ctor_get(v_x_1785_, 1);
v_val_1804_ = lean_ctor_get(v_x_1785_, 2);
v_preresolved_1805_ = lean_ctor_get(v_x_1785_, 3);
v_rawVal_1806_ = lean_ctor_get(v_x_1786_, 1);
v_val_1807_ = lean_ctor_get(v_x_1786_, 2);
v_preresolved_1808_ = lean_ctor_get(v_x_1786_, 3);
lean_inc_ref(v_rawVal_1806_);
lean_inc_ref(v_rawVal_1803_);
v___x_1812_ = lean_substring_beq(v_rawVal_1803_, v_rawVal_1806_);
if (v___x_1812_ == 0)
{
v___y_1810_ = v___x_1812_;
goto v___jp_1809_;
}
else
{
uint8_t v___x_1813_; 
v___x_1813_ = lean_name_eq(v_val_1804_, v_val_1807_);
v___y_1810_ = v___x_1813_;
goto v___jp_1809_;
}
v___jp_1809_:
{
if (v___y_1810_ == 0)
{
return v___y_1810_;
}
else
{
uint8_t v___x_1811_; 
v___x_1811_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_preresolved_1805_, v_preresolved_1808_);
return v___x_1811_;
}
}
}
else
{
uint8_t v___x_1814_; 
v___x_1814_ = 0;
return v___x_1814_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object* v_xs_1815_, lean_object* v_ys_1816_, lean_object* v_x_1817_){
_start:
{
lean_object* v_zero_1818_; uint8_t v_isZero_1819_; 
v_zero_1818_ = lean_unsigned_to_nat(0u);
v_isZero_1819_ = lean_nat_dec_eq(v_x_1817_, v_zero_1818_);
if (v_isZero_1819_ == 1)
{
lean_dec(v_x_1817_);
return v_isZero_1819_;
}
else
{
lean_object* v_one_1820_; lean_object* v_n_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; 
v_one_1820_ = lean_unsigned_to_nat(1u);
v_n_1821_ = lean_nat_sub(v_x_1817_, v_one_1820_);
lean_dec(v_x_1817_);
v___x_1822_ = lean_array_fget_borrowed(v_xs_1815_, v_n_1821_);
v___x_1823_ = lean_array_fget_borrowed(v_ys_1816_, v_n_1821_);
v___x_1824_ = l_Lean_Syntax_structEq(v___x_1822_, v___x_1823_);
if (v___x_1824_ == 0)
{
lean_dec(v_n_1821_);
return v___x_1824_;
}
else
{
v_x_1817_ = v_n_1821_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object* v_xs_1826_, lean_object* v_ys_1827_, lean_object* v_x_1828_){
_start:
{
uint8_t v_res_1829_; lean_object* v_r_1830_; 
v_res_1829_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1826_, v_ys_1827_, v_x_1828_);
lean_dec_ref(v_ys_1827_);
lean_dec_ref(v_xs_1826_);
v_r_1830_ = lean_box(v_res_1829_);
return v_r_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object* v_x_1831_, lean_object* v_x_1832_){
_start:
{
uint8_t v_res_1833_; lean_object* v_r_1834_; 
v_res_1833_ = l_Lean_Syntax_structEq(v_x_1831_, v_x_1832_);
lean_dec(v_x_1832_);
lean_dec(v_x_1831_);
v_r_1834_ = lean_box(v_res_1833_);
return v_r_1834_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object* v_xs_1835_, lean_object* v_ys_1836_, lean_object* v_hsz_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
uint8_t v___x_1840_; 
v___x_1840_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1835_, v_ys_1836_, v_x_1838_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object* v_xs_1841_, lean_object* v_ys_1842_, lean_object* v_hsz_1843_, lean_object* v_x_1844_, lean_object* v_x_1845_){
_start:
{
uint8_t v_res_1846_; lean_object* v_r_1847_; 
v_res_1846_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(v_xs_1841_, v_ys_1842_, v_hsz_1843_, v_x_1844_, v_x_1845_);
lean_dec_ref(v_ys_1842_);
lean_dec_ref(v_xs_1841_);
v_r_1847_ = lean_box(v_res_1846_);
return v_r_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg(){
_start:
{
lean_object* v___f_1852_; 
v___f_1852_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___redArg___closed__0));
return v___f_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg___boxed(lean_object* v___dummy_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Syntax_instBEqTSyntax___redArg();
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object* v_k_1855_){
_start:
{
lean_object* v___f_1856_; 
v___f_1856_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___redArg___closed__0));
return v___f_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object* v_k_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_Syntax_instBEqTSyntax(v_k_1857_);
lean_dec(v_k_1857_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object* v_as_1859_, lean_object* v_i_1860_){
_start:
{
lean_object* v_zero_1861_; uint8_t v_isZero_1862_; 
v_zero_1861_ = lean_unsigned_to_nat(0u);
v_isZero_1862_ = lean_nat_dec_eq(v_i_1860_, v_zero_1861_);
if (v_isZero_1862_ == 1)
{
lean_object* v___x_1863_; 
lean_dec(v_i_1860_);
v___x_1863_ = lean_box(0);
return v___x_1863_;
}
else
{
lean_object* v_one_1864_; lean_object* v_n_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_one_1864_ = lean_unsigned_to_nat(1u);
v_n_1865_ = lean_nat_sub(v_i_1860_, v_one_1864_);
lean_dec(v_i_1860_);
v___x_1866_ = lean_array_fget_borrowed(v_as_1859_, v_n_1865_);
v___x_1867_ = l_Lean_Syntax_getTailInfo_x3f(v___x_1866_);
if (lean_obj_tag(v___x_1867_) == 0)
{
v_i_1860_ = v_n_1865_;
goto _start;
}
else
{
lean_dec(v_n_1865_);
return v___x_1867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object* v_x_1869_){
_start:
{
switch(lean_obj_tag(v_x_1869_))
{
case 2:
{
lean_object* v_info_1870_; lean_object* v___x_1871_; 
v_info_1870_ = lean_ctor_get(v_x_1869_, 0);
lean_inc(v_info_1870_);
v___x_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1871_, 0, v_info_1870_);
return v___x_1871_;
}
case 3:
{
lean_object* v_info_1872_; lean_object* v___x_1873_; 
v_info_1872_ = lean_ctor_get(v_x_1869_, 0);
lean_inc(v_info_1872_);
v___x_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1873_, 0, v_info_1872_);
return v___x_1873_;
}
case 1:
{
lean_object* v_info_1874_; 
v_info_1874_ = lean_ctor_get(v_x_1869_, 0);
if (lean_obj_tag(v_info_1874_) == 2)
{
lean_object* v_args_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_args_1875_ = lean_ctor_get(v_x_1869_, 2);
v___x_1876_ = lean_array_get_size(v_args_1875_);
v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_args_1875_, v___x_1876_);
return v___x_1877_;
}
else
{
lean_object* v___x_1878_; 
lean_inc(v_info_1874_);
v___x_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_info_1874_);
return v___x_1878_;
}
}
default: 
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_box(0);
return v___x_1879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object* v_x_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Syntax_getTailInfo_x3f(v_x_1880_);
lean_dec(v_x_1880_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object* v_as_1882_, lean_object* v_i_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1882_, v_i_1883_);
lean_dec_ref(v_as_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object* v_as_1885_, lean_object* v_i_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1885_, v_i_1886_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object* v_as_1889_, lean_object* v_i_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(v_as_1889_, v_i_1890_, v_a_1891_);
lean_dec_ref(v_as_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object* v_stx_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1893_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_box(2);
return v___x_1895_;
}
else
{
lean_object* v_val_1896_; 
v_val_1896_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_val_1896_);
lean_dec_ref_known(v___x_1894_, 1);
return v_val_1896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object* v_stx_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_Syntax_getTailInfo(v_stx_1897_);
lean_dec(v_stx_1897_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object* v_stx_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1899_);
if (lean_obj_tag(v___x_1900_) == 1)
{
lean_object* v_val_1901_; 
v_val_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_val_1901_);
lean_dec_ref_known(v___x_1900_, 1);
if (lean_obj_tag(v_val_1901_) == 0)
{
lean_object* v_trailing_1902_; lean_object* v_startPos_1903_; lean_object* v_stopPos_1904_; lean_object* v___x_1905_; 
v_trailing_1902_ = lean_ctor_get(v_val_1901_, 2);
lean_inc_ref(v_trailing_1902_);
lean_dec_ref_known(v_val_1901_, 4);
v_startPos_1903_ = lean_ctor_get(v_trailing_1902_, 1);
lean_inc(v_startPos_1903_);
v_stopPos_1904_ = lean_ctor_get(v_trailing_1902_, 2);
lean_inc(v_stopPos_1904_);
lean_dec_ref(v_trailing_1902_);
v___x_1905_ = lean_nat_sub(v_stopPos_1904_, v_startPos_1903_);
lean_dec(v_startPos_1903_);
lean_dec(v_stopPos_1904_);
return v___x_1905_;
}
else
{
lean_object* v___x_1906_; 
lean_dec(v_val_1901_);
v___x_1906_ = lean_unsigned_to_nat(0u);
return v___x_1906_;
}
}
else
{
lean_object* v___x_1907_; 
lean_dec(v___x_1900_);
v___x_1907_ = lean_unsigned_to_nat(0u);
return v___x_1907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object* v_stx_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Syntax_getTrailingSize(v_stx_1908_);
lean_dec(v_stx_1908_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object* v_stx_1910_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = l_Lean_Syntax_getTailInfo(v_stx_1910_);
v___x_1912_ = l_Lean_SourceInfo_getTrailing_x3f(v___x_1911_);
lean_dec(v___x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object* v_stx_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_Syntax_getTrailing_x3f(v_stx_1913_);
lean_dec(v_stx_1913_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object* v_stx_1915_, uint8_t v_canonicalOnly_1916_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = l_Lean_Syntax_getTailInfo(v_stx_1915_);
v___x_1918_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v___x_1917_, v_canonicalOnly_1916_);
lean_dec(v___x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object* v_stx_1919_, lean_object* v_canonicalOnly_1920_){
_start:
{
uint8_t v_canonicalOnly_boxed_1921_; lean_object* v_res_1922_; 
v_canonicalOnly_boxed_1921_ = lean_unbox(v_canonicalOnly_1920_);
v_res_1922_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1919_, v_canonicalOnly_boxed_1921_);
lean_dec(v_stx_1919_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object* v_stx_1923_, uint8_t v_withLeading_1924_, uint8_t v_withTrailing_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_Syntax_getHeadInfo(v_stx_1923_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_leading_1927_; lean_object* v_pos_1928_; lean_object* v___x_1929_; 
v_leading_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc_ref(v_leading_1927_);
v_pos_1928_ = lean_ctor_get(v___x_1926_, 1);
lean_inc(v_pos_1928_);
lean_dec_ref_known(v___x_1926_, 4);
v___x_1929_ = l_Lean_Syntax_getTailInfo(v_stx_1923_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_trailing_1930_; lean_object* v_endPos_1931_; lean_object* v_str_1932_; lean_object* v_startPos_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1947_; 
v_trailing_1930_ = lean_ctor_get(v___x_1929_, 2);
lean_inc_ref(v_trailing_1930_);
v_endPos_1931_ = lean_ctor_get(v___x_1929_, 3);
lean_inc(v_endPos_1931_);
lean_dec_ref_known(v___x_1929_, 4);
v_str_1932_ = lean_ctor_get(v_leading_1927_, 0);
v_startPos_1933_ = lean_ctor_get(v_leading_1927_, 1);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_leading_1927_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; 
v_unused_1948_ = lean_ctor_get(v_leading_1927_, 2);
lean_dec(v_unused_1948_);
v___x_1935_ = v_leading_1927_;
v_isShared_1936_ = v_isSharedCheck_1947_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_startPos_1933_);
lean_inc(v_str_1932_);
lean_dec(v_leading_1927_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1947_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1945_; 
if (v_withLeading_1924_ == 0)
{
lean_dec(v_startPos_1933_);
v___y_1945_ = v_pos_1928_;
goto v___jp_1944_;
}
else
{
lean_dec(v_pos_1928_);
v___y_1945_ = v_startPos_1933_;
goto v___jp_1944_;
}
v___jp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 2, v___y_1939_);
lean_ctor_set(v___x_1935_, 1, v___y_1938_);
v___x_1941_ = v___x_1935_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_str_1932_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v___y_1938_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v___y_1939_);
v___x_1941_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
return v___x_1942_;
}
}
v___jp_1944_:
{
if (v_withTrailing_1925_ == 0)
{
lean_dec_ref(v_trailing_1930_);
v___y_1938_ = v___y_1945_;
v___y_1939_ = v_endPos_1931_;
goto v___jp_1937_;
}
else
{
lean_object* v_stopPos_1946_; 
lean_dec(v_endPos_1931_);
v_stopPos_1946_ = lean_ctor_get(v_trailing_1930_, 2);
lean_inc(v_stopPos_1946_);
lean_dec_ref(v_trailing_1930_);
v___y_1938_ = v___y_1945_;
v___y_1939_ = v_stopPos_1946_;
goto v___jp_1937_;
}
}
}
}
else
{
lean_object* v___x_1949_; 
lean_dec(v___x_1929_);
lean_dec(v_pos_1928_);
lean_dec_ref(v_leading_1927_);
v___x_1949_ = lean_box(0);
return v___x_1949_;
}
}
else
{
lean_object* v___x_1950_; 
lean_dec(v___x_1926_);
v___x_1950_ = lean_box(0);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object* v_stx_1951_, lean_object* v_withLeading_1952_, lean_object* v_withTrailing_1953_){
_start:
{
uint8_t v_withLeading_boxed_1954_; uint8_t v_withTrailing_boxed_1955_; lean_object* v_res_1956_; 
v_withLeading_boxed_1954_ = lean_unbox(v_withLeading_1952_);
v_withTrailing_boxed_1955_ = lean_unbox(v_withTrailing_1953_);
v_res_1956_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1951_, v_withLeading_boxed_1954_, v_withTrailing_boxed_1955_);
lean_dec(v_stx_1951_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object* v_a_1957_, lean_object* v_f_1958_, lean_object* v_i_1959_){
_start:
{
lean_object* v_zero_1960_; uint8_t v_isZero_1961_; 
v_zero_1960_ = lean_unsigned_to_nat(0u);
v_isZero_1961_ = lean_nat_dec_eq(v_i_1959_, v_zero_1960_);
if (v_isZero_1961_ == 1)
{
lean_object* v___x_1962_; 
lean_dec(v_i_1959_);
lean_dec_ref(v_f_1958_);
lean_dec_ref(v_a_1957_);
v___x_1962_ = lean_box(0);
return v___x_1962_;
}
else
{
lean_object* v_one_1963_; lean_object* v_n_1964_; lean_object* v_v_1965_; lean_object* v___x_1966_; 
v_one_1963_ = lean_unsigned_to_nat(1u);
v_n_1964_ = lean_nat_sub(v_i_1959_, v_one_1963_);
lean_dec(v_i_1959_);
v_v_1965_ = lean_array_fget_borrowed(v_a_1957_, v_n_1964_);
lean_inc_ref(v_f_1958_);
lean_inc(v_v_1965_);
v___x_1966_ = lean_apply_1(v_f_1958_, v_v_1965_);
if (lean_obj_tag(v___x_1966_) == 0)
{
v_i_1959_ = v_n_1964_;
goto _start;
}
else
{
lean_object* v_val_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1976_; 
lean_dec_ref(v_f_1958_);
v_val_1968_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1970_ = v___x_1966_;
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_val_1968_);
lean_dec(v___x_1966_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1972_ = lean_array_fset(v_a_1957_, v_n_1964_, v_val_1968_);
lean_dec(v_n_1964_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1972_);
v___x_1974_ = v___x_1970_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object* v_00_u03b1_1977_, lean_object* v_a_1978_, lean_object* v_f_1979_, lean_object* v_i_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(v_a_1978_, v_f_1979_, v_i_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* v_info_1982_, lean_object* v_x_1983_){
_start:
{
switch(lean_obj_tag(v_x_1983_))
{
case 2:
{
lean_object* v_val_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1992_; 
v_val_1984_ = lean_ctor_get(v_x_1983_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_x_1983_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v_x_1983_, 0);
lean_dec(v_unused_1993_);
v___x_1986_ = v_x_1983_;
v_isShared_1987_ = v_isSharedCheck_1992_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_val_1984_);
lean_dec(v_x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1992_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v_info_1982_);
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_info_1982_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_val_1984_);
v___x_1989_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
return v___x_1990_;
}
}
}
case 3:
{
lean_object* v_rawVal_1994_; lean_object* v_val_1995_; lean_object* v_preresolved_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2004_; 
v_rawVal_1994_ = lean_ctor_get(v_x_1983_, 1);
v_val_1995_ = lean_ctor_get(v_x_1983_, 2);
v_preresolved_1996_ = lean_ctor_get(v_x_1983_, 3);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_x_1983_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; 
v_unused_2005_ = lean_ctor_get(v_x_1983_, 0);
lean_dec(v_unused_2005_);
v___x_1998_ = v_x_1983_;
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_preresolved_1996_);
lean_inc(v_val_1995_);
lean_inc(v_rawVal_1994_);
lean_dec(v_x_1983_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v_info_1982_);
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_info_1982_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_rawVal_1994_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_val_1995_);
lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_preresolved_1996_);
v___x_2001_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
return v___x_2002_;
}
}
}
case 1:
{
lean_object* v_info_2006_; lean_object* v_kind_2007_; lean_object* v_args_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2026_; 
v_info_2006_ = lean_ctor_get(v_x_1983_, 0);
v_kind_2007_ = lean_ctor_get(v_x_1983_, 1);
v_args_2008_ = lean_ctor_get(v_x_1983_, 2);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_x_1983_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2010_ = v_x_1983_;
v_isShared_2011_ = v_isSharedCheck_2026_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_args_2008_);
lean_inc(v_kind_2007_);
lean_inc(v_info_2006_);
lean_dec(v_x_1983_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2026_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_array_get_size(v_args_2008_);
v___x_2013_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(v_info_1982_, v_args_2008_, v___x_2012_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v___x_2014_; 
lean_del_object(v___x_2010_);
lean_dec(v_kind_2007_);
lean_dec(v_info_2006_);
v___x_2014_ = lean_box(0);
return v___x_2014_;
}
else
{
lean_object* v_val_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2025_; 
v_val_2015_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2017_ = v___x_2013_;
v_isShared_2018_ = v_isSharedCheck_2025_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_val_2015_);
lean_dec(v___x_2013_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2025_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 2, v_val_2015_);
v___x_2020_ = v___x_2010_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_info_2006_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_kind_2007_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v_val_2015_);
v___x_2020_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2022_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2020_);
v___x_2022_ = v___x_2017_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2027_; 
lean_dec(v_x_1983_);
lean_dec(v_info_1982_);
v___x_2027_ = lean_box(0);
return v___x_2027_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object* v_info_2028_, lean_object* v_a_2029_, lean_object* v_i_2030_){
_start:
{
lean_object* v_zero_2031_; uint8_t v_isZero_2032_; 
v_zero_2031_ = lean_unsigned_to_nat(0u);
v_isZero_2032_ = lean_nat_dec_eq(v_i_2030_, v_zero_2031_);
if (v_isZero_2032_ == 1)
{
lean_object* v___x_2033_; 
lean_dec(v_i_2030_);
lean_dec_ref(v_a_2029_);
lean_dec(v_info_2028_);
v___x_2033_ = lean_box(0);
return v___x_2033_;
}
else
{
lean_object* v_one_2034_; lean_object* v_n_2035_; lean_object* v_v_2036_; lean_object* v___x_2037_; 
v_one_2034_ = lean_unsigned_to_nat(1u);
v_n_2035_ = lean_nat_sub(v_i_2030_, v_one_2034_);
lean_dec(v_i_2030_);
v_v_2036_ = lean_array_fget_borrowed(v_a_2029_, v_n_2035_);
lean_inc(v_v_2036_);
lean_inc(v_info_2028_);
v___x_2037_ = l_Lean_Syntax_setTailInfoAux(v_info_2028_, v_v_2036_);
if (lean_obj_tag(v___x_2037_) == 0)
{
v_i_2030_ = v_n_2035_;
goto _start;
}
else
{
lean_object* v_val_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_info_2028_);
v_val_2039_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2041_ = v___x_2037_;
v_isShared_2042_ = v_isSharedCheck_2047_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_val_2039_);
lean_dec(v___x_2037_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2047_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2043_ = lean_array_fset(v_a_2029_, v_n_2035_, v_val_2039_);
lean_dec(v_n_2035_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2043_);
v___x_2045_ = v___x_2041_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object* v_stx_2048_, lean_object* v_info_2049_){
_start:
{
lean_object* v___x_2050_; 
lean_inc(v_stx_2048_);
v___x_2050_ = l_Lean_Syntax_setTailInfoAux(v_info_2049_, v_stx_2048_);
if (lean_obj_tag(v___x_2050_) == 0)
{
return v_stx_2048_;
}
else
{
lean_object* v_val_2051_; 
lean_dec(v_stx_2048_);
v_val_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_val_2051_);
lean_dec_ref_known(v___x_2050_, 1);
return v_val_2051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object* v_stx_2052_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Lean_Syntax_getTailInfo(v_stx_2052_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_trailing_2054_; lean_object* v_leading_2055_; lean_object* v_pos_2056_; lean_object* v_endPos_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2075_; 
v_trailing_2054_ = lean_ctor_get(v___x_2053_, 2);
v_leading_2055_ = lean_ctor_get(v___x_2053_, 0);
v_pos_2056_ = lean_ctor_get(v___x_2053_, 1);
v_endPos_2057_ = lean_ctor_get(v___x_2053_, 3);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2059_ = v___x_2053_;
v_isShared_2060_ = v_isSharedCheck_2075_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_endPos_2057_);
lean_inc(v_trailing_2054_);
lean_inc(v_pos_2056_);
lean_inc(v_leading_2055_);
lean_dec(v___x_2053_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2075_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_str_2061_; lean_object* v_startPos_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2073_; 
v_str_2061_ = lean_ctor_get(v_trailing_2054_, 0);
v_startPos_2062_ = lean_ctor_get(v_trailing_2054_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_trailing_2054_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v_trailing_2054_, 2);
lean_dec(v_unused_2074_);
v___x_2064_ = v_trailing_2054_;
v_isShared_2065_ = v_isSharedCheck_2073_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_startPos_2062_);
lean_inc(v_str_2061_);
lean_dec(v_trailing_2054_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2073_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
lean_inc(v_startPos_2062_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 2, v_startPos_2062_);
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_str_2061_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_startPos_2062_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v_startPos_2062_);
v___x_2067_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2069_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 2, v___x_2067_);
v___x_2069_ = v___x_2059_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_leading_2055_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_pos_2056_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_endPos_2057_);
v___x_2069_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_Syntax_setTailInfo(v_stx_2052_, v___x_2069_);
return v___x_2070_;
}
}
}
}
}
else
{
lean_dec(v___x_2053_);
return v_stx_2052_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object* v_a_2076_, lean_object* v_f_2077_, lean_object* v_i_2078_){
_start:
{
lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2079_ = lean_array_get_size(v_a_2076_);
v___x_2080_ = lean_nat_dec_lt(v_i_2078_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; 
lean_dec(v_i_2078_);
lean_dec_ref(v_f_2077_);
lean_dec_ref(v_a_2076_);
v___x_2081_ = lean_box(0);
return v___x_2081_;
}
else
{
lean_object* v_v_2082_; lean_object* v___x_2083_; 
v_v_2082_ = lean_array_fget_borrowed(v_a_2076_, v_i_2078_);
lean_inc_ref(v_f_2077_);
lean_inc(v_v_2082_);
v___x_2083_ = lean_apply_1(v_f_2077_, v_v_2082_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_unsigned_to_nat(1u);
v___x_2085_ = lean_nat_add(v_i_2078_, v___x_2084_);
lean_dec(v_i_2078_);
v_i_2078_ = v___x_2085_;
goto _start;
}
else
{
lean_object* v_val_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v_f_2077_);
v_val_2087_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2089_ = v___x_2083_;
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_val_2087_);
lean_dec(v___x_2083_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = lean_array_fset(v_a_2076_, v_i_2078_, v_val_2087_);
lean_dec(v_i_2078_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2091_);
v___x_2093_ = v___x_2089_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object* v_00_u03b1_2096_, lean_object* v_inst_2097_, lean_object* v_a_2098_, lean_object* v_f_2099_, lean_object* v_i_2100_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(v_a_2098_, v_f_2099_, v_i_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object* v_00_u03b1_2102_, lean_object* v_inst_2103_, lean_object* v_a_2104_, lean_object* v_f_2105_, lean_object* v_i_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(v_00_u03b1_2102_, v_inst_2103_, v_a_2104_, v_f_2105_, v_i_2106_);
lean_dec(v_inst_2103_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object* v_info_2108_, lean_object* v_x_2109_){
_start:
{
switch(lean_obj_tag(v_x_2109_))
{
case 2:
{
lean_object* v_val_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2118_; 
v_val_2110_ = lean_ctor_get(v_x_2109_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_x_2109_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; 
v_unused_2119_ = lean_ctor_get(v_x_2109_, 0);
lean_dec(v_unused_2119_);
v___x_2112_ = v_x_2109_;
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_val_2110_);
lean_dec(v_x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v_info_2108_);
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_info_2108_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_val_2110_);
v___x_2115_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2116_; 
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
return v___x_2116_;
}
}
}
case 3:
{
lean_object* v_rawVal_2120_; lean_object* v_val_2121_; lean_object* v_preresolved_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2130_; 
v_rawVal_2120_ = lean_ctor_get(v_x_2109_, 1);
v_val_2121_ = lean_ctor_get(v_x_2109_, 2);
v_preresolved_2122_ = lean_ctor_get(v_x_2109_, 3);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_x_2109_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v_x_2109_, 0);
lean_dec(v_unused_2131_);
v___x_2124_ = v_x_2109_;
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_preresolved_2122_);
lean_inc(v_val_2121_);
lean_inc(v_rawVal_2120_);
lean_dec(v_x_2109_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v_info_2108_);
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_info_2108_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_rawVal_2120_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_val_2121_);
lean_ctor_set(v_reuseFailAlloc_2129_, 3, v_preresolved_2122_);
v___x_2127_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
return v___x_2128_;
}
}
}
case 1:
{
lean_object* v_info_2132_; lean_object* v_kind_2133_; lean_object* v_args_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2152_; 
v_info_2132_ = lean_ctor_get(v_x_2109_, 0);
v_kind_2133_ = lean_ctor_get(v_x_2109_, 1);
v_args_2134_ = lean_ctor_get(v_x_2109_, 2);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_x_2109_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2136_ = v_x_2109_;
v_isShared_2137_ = v_isSharedCheck_2152_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_args_2134_);
lean_inc(v_kind_2133_);
lean_inc(v_info_2132_);
lean_dec(v_x_2109_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2152_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = lean_unsigned_to_nat(0u);
v___x_2139_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(v_info_2108_, v_args_2134_, v___x_2138_);
if (lean_obj_tag(v___x_2139_) == 1)
{
lean_object* v_val_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2150_; 
v_val_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2150_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_val_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2150_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 2, v_val_2140_);
v___x_2145_ = v___x_2136_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_info_2132_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_kind_2133_);
lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_val_2140_);
v___x_2145_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2147_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2145_);
v___x_2147_ = v___x_2142_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
lean_object* v___x_2151_; 
lean_dec(v___x_2139_);
lean_del_object(v___x_2136_);
lean_dec(v_kind_2133_);
lean_dec(v_info_2132_);
v___x_2151_ = lean_box(0);
return v___x_2151_;
}
}
}
default: 
{
lean_object* v___x_2153_; 
lean_dec(v_x_2109_);
lean_dec(v_info_2108_);
v___x_2153_ = lean_box(0);
return v___x_2153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object* v_info_2154_, lean_object* v_a_2155_, lean_object* v_i_2156_){
_start:
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = lean_array_get_size(v_a_2155_);
v___x_2158_ = lean_nat_dec_lt(v_i_2156_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; 
lean_dec(v_i_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_info_2154_);
v___x_2159_ = lean_box(0);
return v___x_2159_;
}
else
{
lean_object* v_v_2160_; lean_object* v___x_2161_; 
v_v_2160_ = lean_array_fget_borrowed(v_a_2155_, v_i_2156_);
lean_inc(v_v_2160_);
lean_inc(v_info_2154_);
v___x_2161_ = l_Lean_Syntax_setHeadInfoAux(v_info_2154_, v_v_2160_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_unsigned_to_nat(1u);
v___x_2163_ = lean_nat_add(v_i_2156_, v___x_2162_);
lean_dec(v_i_2156_);
v_i_2156_ = v___x_2163_;
goto _start;
}
else
{
lean_object* v_val_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2173_; 
lean_dec(v_info_2154_);
v_val_2165_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2167_ = v___x_2161_;
v_isShared_2168_ = v_isSharedCheck_2173_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_val_2165_);
lean_dec(v___x_2161_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2173_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = lean_array_fset(v_a_2155_, v_i_2156_, v_val_2165_);
lean_dec(v_i_2156_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2169_);
v___x_2171_ = v___x_2167_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object* v_stx_2174_, lean_object* v_info_2175_){
_start:
{
lean_object* v___x_2176_; 
lean_inc(v_stx_2174_);
v___x_2176_ = l_Lean_Syntax_setHeadInfoAux(v_info_2175_, v_stx_2174_);
if (lean_obj_tag(v___x_2176_) == 0)
{
return v_stx_2174_;
}
else
{
lean_object* v_val_2177_; 
lean_dec(v_stx_2174_);
v_val_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_val_2177_);
lean_dec_ref_known(v___x_2176_, 1);
return v_val_2177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object* v_info_2178_, lean_object* v_x_2179_){
_start:
{
switch(lean_obj_tag(v_x_2179_))
{
case 0:
{
lean_dec(v_info_2178_);
return v_x_2179_;
}
case 1:
{
lean_object* v_kind_2180_; lean_object* v_args_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
v_kind_2180_ = lean_ctor_get(v_x_2179_, 1);
v_args_2181_ = lean_ctor_get(v_x_2179_, 2);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_x_2179_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; 
v_unused_2189_ = lean_ctor_get(v_x_2179_, 0);
lean_dec(v_unused_2189_);
v___x_2183_ = v_x_2179_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_args_2181_);
lean_inc(v_kind_2180_);
lean_dec(v_x_2179_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v_info_2178_);
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_info_2178_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_kind_2180_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_args_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
case 2:
{
lean_object* v_val_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
v_val_2190_ = lean_ctor_get(v_x_2179_, 1);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_x_2179_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v_x_2179_, 0);
lean_dec(v_unused_2198_);
v___x_2192_ = v_x_2179_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_val_2190_);
lean_dec(v_x_2179_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v_info_2178_);
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_info_2178_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_val_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
default: 
{
lean_object* v_rawVal_2199_; lean_object* v_val_2200_; lean_object* v_preresolved_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
v_rawVal_2199_ = lean_ctor_get(v_x_2179_, 1);
v_val_2200_ = lean_ctor_get(v_x_2179_, 2);
v_preresolved_2201_ = lean_ctor_get(v_x_2179_, 3);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_x_2179_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; 
v_unused_2209_ = lean_ctor_get(v_x_2179_, 0);
lean_dec(v_unused_2209_);
v___x_2203_ = v_x_2179_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_preresolved_2201_);
lean_inc(v_val_2200_);
lean_inc(v_rawVal_2199_);
lean_dec(v_x_2179_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v_info_2178_);
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_info_2178_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_rawVal_2199_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v_val_2200_);
lean_ctor_set(v_reuseFailAlloc_2207_, 3, v_preresolved_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object* v_x_2213_){
_start:
{
switch(lean_obj_tag(v_x_2213_))
{
case 2:
{
lean_object* v_info_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; 
v_info_2214_ = lean_ctor_get(v_x_2213_, 0);
v___x_2215_ = 0;
v___x_2216_ = l_Lean_SourceInfo_getPos_x3f(v_info_2214_, v___x_2215_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v___x_2217_; 
lean_dec_ref_known(v_x_2213_, 2);
v___x_2217_ = lean_box(0);
return v___x_2217_;
}
else
{
lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; 
v_unused_2225_ = lean_ctor_get(v___x_2216_, 0);
lean_dec(v_unused_2225_);
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v_x_2213_);
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_x_2213_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
case 3:
{
lean_object* v_info_2226_; uint8_t v___x_2227_; lean_object* v___x_2228_; 
v_info_2226_ = lean_ctor_get(v_x_2213_, 0);
v___x_2227_ = 0;
v___x_2228_ = l_Lean_SourceInfo_getPos_x3f(v_info_2226_, v___x_2227_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v___x_2229_; 
lean_dec_ref_known(v_x_2213_, 4);
v___x_2229_ = lean_box(0);
return v___x_2229_;
}
else
{
lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2236_ == 0)
{
lean_object* v_unused_2237_; 
v_unused_2237_ = lean_ctor_get(v___x_2228_, 0);
lean_dec(v_unused_2237_);
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v_x_2213_);
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_x_2213_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
case 1:
{
lean_object* v_info_2238_; 
v_info_2238_ = lean_ctor_get(v_x_2213_, 0);
if (lean_obj_tag(v_info_2238_) == 2)
{
lean_object* v_args_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; size_t v_sz_2242_; size_t v___x_2243_; lean_object* v___x_2244_; lean_object* v_fst_2245_; 
v_args_2239_ = lean_ctor_get(v_x_2213_, 2);
lean_inc_ref(v_args_2239_);
lean_dec_ref_known(v_x_2213_, 3);
v___x_2240_ = lean_box(0);
v___x_2241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_2242_ = lean_array_size(v_args_2239_);
v___x_2243_ = ((size_t)0ULL);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_args_2239_, v_sz_2242_, v___x_2243_, v___x_2241_);
lean_dec_ref(v_args_2239_);
v_fst_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_fst_2245_);
lean_dec_ref(v___x_2244_);
if (lean_obj_tag(v_fst_2245_) == 0)
{
return v___x_2240_;
}
else
{
lean_object* v_val_2246_; 
v_val_2246_ = lean_ctor_get(v_fst_2245_, 0);
lean_inc(v_val_2246_);
lean_dec_ref_known(v_fst_2245_, 1);
return v_val_2246_;
}
}
else
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2247_, 0, v_x_2213_);
return v___x_2247_;
}
}
default: 
{
lean_object* v___x_2248_; 
lean_dec(v_x_2213_);
v___x_2248_ = lean_box(0);
return v___x_2248_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object* v_as_2249_, size_t v_sz_2250_, size_t v_i_2251_, lean_object* v_b_2252_){
_start:
{
uint8_t v___x_2253_; 
v___x_2253_ = lean_usize_dec_lt(v_i_2251_, v_sz_2250_);
if (v___x_2253_ == 0)
{
lean_inc_ref(v_b_2252_);
return v_b_2252_;
}
else
{
lean_object* v___x_2254_; lean_object* v_a_2255_; lean_object* v___x_2256_; 
v___x_2254_ = lean_box(0);
v_a_2255_ = lean_array_uget_borrowed(v_as_2249_, v_i_2251_);
lean_inc(v_a_2255_);
v___x_2256_ = l_Lean_Syntax_getHead_x3f(v_a_2255_);
if (lean_obj_tag(v___x_2256_) == 1)
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
v___x_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set(v___x_2258_, 1, v___x_2254_);
return v___x_2258_;
}
else
{
lean_object* v___x_2259_; size_t v___x_2260_; size_t v___x_2261_; 
lean_dec(v___x_2256_);
v___x_2259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_2260_ = ((size_t)1ULL);
v___x_2261_ = lean_usize_add(v_i_2251_, v___x_2260_);
v_i_2251_ = v___x_2261_;
v_b_2252_ = v___x_2259_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object* v_as_2263_, lean_object* v_sz_2264_, lean_object* v_i_2265_, lean_object* v_b_2266_){
_start:
{
size_t v_sz_boxed_2267_; size_t v_i_boxed_2268_; lean_object* v_res_2269_; 
v_sz_boxed_2267_ = lean_unbox_usize(v_sz_2264_);
lean_dec(v_sz_2264_);
v_i_boxed_2268_ = lean_unbox_usize(v_i_2265_);
lean_dec(v_i_2265_);
v_res_2269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_as_2263_, v_sz_boxed_2267_, v_i_boxed_2268_, v_b_2266_);
lean_dec_ref(v_b_2266_);
lean_dec_ref(v_as_2263_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object* v_target_2270_, lean_object* v_source_2271_){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2272_ = l_Lean_Syntax_getHeadInfo(v_source_2271_);
v___x_2273_ = l_Lean_Syntax_setHeadInfo(v_target_2270_, v___x_2272_);
v___x_2274_ = l_Lean_Syntax_getTailInfo(v_source_2271_);
v___x_2275_ = l_Lean_Syntax_setTailInfo(v___x_2273_, v___x_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object* v_target_2276_, lean_object* v_source_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_target_2276_, v_source_2277_);
lean_dec(v_source_2277_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object* v_stx_2279_){
_start:
{
uint8_t v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = 0;
v___x_2281_ = l_Lean_SourceInfo_fromRef(v_stx_2279_, v___x_2280_);
v___x_2282_ = l_Lean_Syntax_setHeadInfo(v_stx_2279_, v___x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object* v_val_2283_, lean_object* v_withRef_2284_, lean_object* v_x_2285_, lean_object* v_oldRef_2286_){
_start:
{
lean_object* v_ref_2287_; lean_object* v___x_2288_; 
v_ref_2287_ = l_Lean_replaceRef(v_val_2283_, v_oldRef_2286_);
v___x_2288_ = lean_apply_3(v_withRef_2284_, lean_box(0), v_ref_2287_, v_x_2285_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object* v_val_2289_, lean_object* v_withRef_2290_, lean_object* v_x_2291_, lean_object* v_oldRef_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_withHeadRefOnly___redArg___lam__0(v_val_2289_, v_withRef_2290_, v_x_2291_, v_oldRef_2292_);
lean_dec(v_oldRef_2292_);
lean_dec(v_val_2289_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object* v_x_2294_, lean_object* v_withRef_2295_, lean_object* v_toBind_2296_, lean_object* v_getRef_2297_, lean_object* v_____do__lift_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_Syntax_getHead_x3f(v_____do__lift_2298_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_dec(v_getRef_2297_);
lean_dec(v_toBind_2296_);
lean_dec(v_withRef_2295_);
return v_x_2294_;
}
else
{
lean_object* v_val_2300_; lean_object* v___f_2301_; lean_object* v___x_2302_; 
v_val_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_val_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___f_2301_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2301_, 0, v_val_2300_);
lean_closure_set(v___f_2301_, 1, v_withRef_2295_);
lean_closure_set(v___f_2301_, 2, v_x_2294_);
v___x_2302_ = lean_apply_4(v_toBind_2296_, lean_box(0), lean_box(0), v_getRef_2297_, v___f_2301_);
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object* v_inst_2303_, lean_object* v_inst_2304_, lean_object* v_x_2305_){
_start:
{
lean_object* v_toBind_2306_; lean_object* v_getRef_2307_; lean_object* v_withRef_2308_; lean_object* v___f_2309_; lean_object* v___x_2310_; 
v_toBind_2306_ = lean_ctor_get(v_inst_2303_, 1);
lean_inc_n(v_toBind_2306_, 2);
lean_dec_ref(v_inst_2303_);
v_getRef_2307_ = lean_ctor_get(v_inst_2304_, 0);
lean_inc_n(v_getRef_2307_, 2);
v_withRef_2308_ = lean_ctor_get(v_inst_2304_, 1);
lean_inc(v_withRef_2308_);
lean_dec_ref(v_inst_2304_);
v___f_2309_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2309_, 0, v_x_2305_);
lean_closure_set(v___f_2309_, 1, v_withRef_2308_);
lean_closure_set(v___f_2309_, 2, v_toBind_2306_);
lean_closure_set(v___f_2309_, 3, v_getRef_2307_);
v___x_2310_ = lean_apply_4(v_toBind_2306_, lean_box(0), lean_box(0), v_getRef_2307_, v___f_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object* v_m_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_00_u03b1_2314_, lean_object* v_x_2315_){
_start:
{
lean_object* v_toBind_2316_; lean_object* v_getRef_2317_; lean_object* v_withRef_2318_; lean_object* v___f_2319_; lean_object* v___x_2320_; 
v_toBind_2316_ = lean_ctor_get(v_inst_2312_, 1);
lean_inc_n(v_toBind_2316_, 2);
lean_dec_ref(v_inst_2312_);
v_getRef_2317_ = lean_ctor_get(v_inst_2313_, 0);
lean_inc_n(v_getRef_2317_, 2);
v_withRef_2318_ = lean_ctor_get(v_inst_2313_, 1);
lean_inc(v_withRef_2318_);
lean_dec_ref(v_inst_2313_);
v___f_2319_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2319_, 0, v_x_2315_);
lean_closure_set(v___f_2319_, 1, v_withRef_2318_);
lean_closure_set(v___f_2319_, 2, v_toBind_2316_);
lean_closure_set(v___f_2319_, 3, v_getRef_2317_);
v___x_2320_ = lean_apply_4(v_toBind_2316_, lean_box(0), lean_box(0), v_getRef_2317_, v___f_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(uint8_t v___x_2330_, lean_object* v_k_2331_){
_start:
{
lean_object* v___x_2332_; uint8_t v___x_2333_; 
v___x_2332_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_2333_ = lean_name_eq(v_k_2331_, v___x_2332_);
if (v___x_2333_ == 0)
{
return v___x_2330_;
}
else
{
uint8_t v___x_2334_; 
v___x_2334_ = 0;
return v___x_2334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object* v___x_2335_, lean_object* v_k_2336_){
_start:
{
uint8_t v___x_1783__boxed_2337_; uint8_t v_res_2338_; lean_object* v_r_2339_; 
v___x_1783__boxed_2337_ = lean_unbox(v___x_2335_);
v_res_2338_ = l_Lean_expandMacros___lam__0(v___x_1783__boxed_2337_, v_k_2336_);
lean_dec(v_k_2336_);
v_r_2339_ = lean_box(v_res_2338_);
return v_r_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object* v_stx_2341_, lean_object* v_p_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
if (lean_obj_tag(v_stx_2341_) == 1)
{
lean_object* v_info_2345_; lean_object* v_kind_2346_; lean_object* v_args_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v_info_2345_ = lean_ctor_get(v_stx_2341_, 0);
v_kind_2346_ = lean_ctor_get(v_stx_2341_, 1);
v_args_2347_ = lean_ctor_get(v_stx_2341_, 2);
lean_inc(v_kind_2346_);
v___x_2348_ = lean_apply_1(v_p_2342_, v_kind_2346_);
v___x_2349_ = lean_unbox(v___x_2348_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; 
lean_dec_ref(v_a_2343_);
v___x_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2350_, 0, v_stx_2341_);
lean_ctor_set(v___x_2350_, 1, v_a_2344_);
return v___x_2350_;
}
else
{
lean_object* v_methods_2351_; lean_object* v_quotContext_2352_; lean_object* v_currMacroScope_2353_; lean_object* v_currRecDepth_2354_; lean_object* v_maxRecDepth_2355_; lean_object* v_ref_2356_; lean_object* v_ref_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_methods_2351_ = lean_ctor_get(v_a_2343_, 0);
lean_inc_n(v_methods_2351_, 2);
v_quotContext_2352_ = lean_ctor_get(v_a_2343_, 1);
lean_inc_n(v_quotContext_2352_, 2);
v_currMacroScope_2353_ = lean_ctor_get(v_a_2343_, 2);
lean_inc_n(v_currMacroScope_2353_, 2);
v_currRecDepth_2354_ = lean_ctor_get(v_a_2343_, 3);
lean_inc_n(v_currRecDepth_2354_, 2);
v_maxRecDepth_2355_ = lean_ctor_get(v_a_2343_, 4);
lean_inc_n(v_maxRecDepth_2355_, 2);
v_ref_2356_ = lean_ctor_get(v_a_2343_, 5);
lean_inc(v_ref_2356_);
lean_dec_ref(v_a_2343_);
v_ref_2357_ = l_Lean_replaceRef(v_stx_2341_, v_ref_2356_);
lean_dec(v_ref_2356_);
lean_inc(v_ref_2357_);
v___x_2358_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2358_, 0, v_methods_2351_);
lean_ctor_set(v___x_2358_, 1, v_quotContext_2352_);
lean_ctor_set(v___x_2358_, 2, v_currMacroScope_2353_);
lean_ctor_set(v___x_2358_, 3, v_currRecDepth_2354_);
lean_ctor_set(v___x_2358_, 4, v_maxRecDepth_2355_);
lean_ctor_set(v___x_2358_, 5, v_ref_2357_);
lean_inc_ref(v_stx_2341_);
v___x_2359_ = l_Lean_Macro_expandMacro_x3f(v_stx_2341_, v___x_2358_, v_a_2344_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
if (lean_obj_tag(v_a_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref_known(v___x_2358_, 6);
v_a_2361_ = lean_ctor_get(v___x_2359_, 1);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; 
v_unused_2407_ = lean_ctor_get(v___x_2359_, 0);
lean_dec(v_unused_2407_);
v___x_2363_ = v___x_2359_;
v_isShared_2364_ = v_isSharedCheck_2406_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2359_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2406_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
uint8_t v___x_2365_; 
v___x_2365_ = lean_nat_dec_eq(v_currRecDepth_2354_, v_maxRecDepth_2355_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2397_; 
lean_inc_ref(v_args_2347_);
lean_inc(v_kind_2346_);
lean_inc(v_info_2345_);
lean_del_object(v___x_2363_);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_stx_2341_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; lean_object* v_unused_2399_; lean_object* v_unused_2400_; 
v_unused_2398_ = lean_ctor_get(v_stx_2341_, 2);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_stx_2341_, 1);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_stx_2341_, 0);
lean_dec(v_unused_2400_);
v___x_2367_ = v_stx_2341_;
v_isShared_2368_ = v_isSharedCheck_2397_;
goto v_resetjp_2366_;
}
else
{
lean_dec(v_stx_2341_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2397_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; size_t v_sz_2372_; size_t v___x_2373_; uint8_t v___x_2374_; lean_object* v___x_2375_; 
v___x_2369_ = lean_unsigned_to_nat(1u);
v___x_2370_ = lean_nat_add(v_currRecDepth_2354_, v___x_2369_);
lean_dec(v_currRecDepth_2354_);
v___x_2371_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2371_, 0, v_methods_2351_);
lean_ctor_set(v___x_2371_, 1, v_quotContext_2352_);
lean_ctor_set(v___x_2371_, 2, v_currMacroScope_2353_);
lean_ctor_set(v___x_2371_, 3, v___x_2370_);
lean_ctor_set(v___x_2371_, 4, v_maxRecDepth_2355_);
lean_ctor_set(v___x_2371_, 5, v_ref_2357_);
v_sz_2372_ = lean_array_size(v_args_2347_);
v___x_2373_ = ((size_t)0ULL);
v___x_2374_ = lean_unbox(v___x_2348_);
v___x_2375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2374_, v_sz_2372_, v___x_2373_, v_args_2347_, v___x_2371_, v_a_2361_);
lean_dec_ref_known(v___x_2371_, 6);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2387_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_a_2377_ = lean_ctor_get(v___x_2375_, 1);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2379_ = v___x_2375_;
v_isShared_2380_ = v_isSharedCheck_2387_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2387_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 2, v_a_2376_);
v___x_2382_ = v___x_2367_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_info_2345_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_kind_2346_);
lean_ctor_set(v_reuseFailAlloc_2386_, 2, v_a_2376_);
v___x_2382_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2384_; 
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2382_);
v___x_2384_ = v___x_2379_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_a_2377_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_del_object(v___x_2367_);
lean_dec(v_kind_2346_);
lean_dec(v_info_2345_);
v_a_2388_ = lean_ctor_get(v___x_2375_, 0);
v_a_2389_ = lean_ctor_get(v___x_2375_, 1);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2375_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_inc(v_a_2388_);
lean_dec(v___x_2375_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2388_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
else
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
lean_dec(v_ref_2357_);
lean_dec(v_maxRecDepth_2355_);
lean_dec(v_currRecDepth_2354_);
lean_dec(v_currMacroScope_2353_);
lean_dec(v_quotContext_2352_);
lean_dec(v_methods_2351_);
v___x_2401_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_stx_2341_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set_tag(v___x_2363_, 1);
lean_ctor_set(v___x_2363_, 0, v___x_2402_);
v___x_2404_ = v___x_2363_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_a_2361_);
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
else
{
lean_object* v_a_2408_; lean_object* v_val_2409_; lean_object* v___f_2410_; 
lean_dec(v_ref_2357_);
lean_dec(v_maxRecDepth_2355_);
lean_dec(v_currRecDepth_2354_);
lean_dec(v_currMacroScope_2353_);
lean_dec(v_quotContext_2352_);
lean_dec(v_methods_2351_);
lean_dec_ref_known(v_stx_2341_, 3);
v_a_2408_ = lean_ctor_get(v___x_2359_, 1);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2359_, 2);
v_val_2409_ = lean_ctor_get(v_a_2360_, 0);
lean_inc(v_val_2409_);
lean_dec_ref_known(v_a_2360_, 1);
v___f_2410_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2410_, 0, v___x_2348_);
v_stx_2341_ = v_val_2409_;
v_p_2342_ = v___f_2410_;
v_a_2343_ = v___x_2358_;
v_a_2344_ = v_a_2408_;
goto _start;
}
}
else
{
lean_object* v_a_2412_; lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec_ref_known(v___x_2358_, 6);
lean_dec(v_ref_2357_);
lean_dec(v_maxRecDepth_2355_);
lean_dec(v_currRecDepth_2354_);
lean_dec(v_currMacroScope_2353_);
lean_dec(v_quotContext_2352_);
lean_dec(v_methods_2351_);
lean_dec_ref_known(v_stx_2341_, 3);
v_a_2412_ = lean_ctor_get(v___x_2359_, 0);
v_a_2413_ = lean_ctor_get(v___x_2359_, 1);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2359_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_inc(v_a_2412_);
lean_dec(v___x_2359_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2412_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
else
{
lean_object* v___x_2421_; 
lean_dec_ref(v_a_2343_);
lean_dec_ref(v_p_2342_);
v___x_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2421_, 0, v_stx_2341_);
lean_ctor_set(v___x_2421_, 1, v_a_2344_);
return v___x_2421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t v___x_2422_, size_t v_sz_2423_, size_t v_i_2424_, lean_object* v_bs_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
uint8_t v___x_2428_; 
v___x_2428_ = lean_usize_dec_lt(v_i_2424_, v_sz_2423_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; 
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v_bs_2425_);
lean_ctor_set(v___x_2429_, 1, v___y_2427_);
return v___x_2429_;
}
else
{
lean_object* v___x_2430_; lean_object* v___f_2431_; lean_object* v_v_2432_; lean_object* v___x_2433_; 
v___x_2430_ = lean_box(v___x_2422_);
v___f_2431_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2431_, 0, v___x_2430_);
v_v_2432_ = lean_array_uget_borrowed(v_bs_2425_, v_i_2424_);
lean_inc_ref(v___y_2426_);
lean_inc(v_v_2432_);
v___x_2433_ = l_Lean_expandMacros(v_v_2432_, v___f_2431_, v___y_2426_, v___y_2427_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v_a_2435_; lean_object* v___x_2436_; lean_object* v_bs_x27_2437_; size_t v___x_2438_; size_t v___x_2439_; lean_object* v___x_2440_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2434_);
v_a_2435_ = lean_ctor_get(v___x_2433_, 1);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2433_, 2);
v___x_2436_ = lean_unsigned_to_nat(0u);
v_bs_x27_2437_ = lean_array_uset(v_bs_2425_, v_i_2424_, v___x_2436_);
v___x_2438_ = ((size_t)1ULL);
v___x_2439_ = lean_usize_add(v_i_2424_, v___x_2438_);
v___x_2440_ = lean_array_uset(v_bs_x27_2437_, v_i_2424_, v_a_2434_);
v_i_2424_ = v___x_2439_;
v_bs_2425_ = v___x_2440_;
v___y_2427_ = v_a_2435_;
goto _start;
}
else
{
lean_object* v_a_2442_; lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec_ref(v_bs_2425_);
v_a_2442_ = lean_ctor_get(v___x_2433_, 0);
v_a_2443_ = lean_ctor_get(v___x_2433_, 1);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2433_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_inc(v_a_2442_);
lean_dec(v___x_2433_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2442_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object* v___x_2451_, lean_object* v_sz_2452_, lean_object* v_i_2453_, lean_object* v_bs_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
uint8_t v___x_1802__boxed_2457_; size_t v_sz_boxed_2458_; size_t v_i_boxed_2459_; lean_object* v_res_2460_; 
v___x_1802__boxed_2457_ = lean_unbox(v___x_2451_);
v_sz_boxed_2458_ = lean_unbox_usize(v_sz_2452_);
lean_dec(v_sz_2452_);
v_i_boxed_2459_ = lean_unbox_usize(v_i_2453_);
lean_dec(v_i_2453_);
v_res_2460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_1802__boxed_2457_, v_sz_boxed_2458_, v_i_boxed_2459_, v_bs_2454_, v___y_2455_, v___y_2456_);
lean_dec_ref(v___y_2455_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object* v_src_2461_, lean_object* v_val_2462_, uint8_t v_canonical_2463_){
_start:
{
lean_object* v___x_2464_; uint8_t v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2464_ = l_Lean_SourceInfo_fromRef(v_src_2461_, v_canonical_2463_);
v___x_2465_ = 1;
lean_inc(v_val_2462_);
v___x_2466_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2462_, v___x_2465_);
v___x_2467_ = lean_unsigned_to_nat(0u);
v___x_2468_ = lean_string_utf8_byte_size(v___x_2466_);
v___x_2469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2466_);
lean_ctor_set(v___x_2469_, 1, v___x_2467_);
lean_ctor_set(v___x_2469_, 2, v___x_2468_);
v___x_2470_ = lean_box(0);
v___x_2471_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2464_);
lean_ctor_set(v___x_2471_, 1, v___x_2469_);
lean_ctor_set(v___x_2471_, 2, v_val_2462_);
lean_ctor_set(v___x_2471_, 3, v___x_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object* v_src_2472_, lean_object* v_val_2473_, lean_object* v_canonical_2474_){
_start:
{
uint8_t v_canonical_boxed_2475_; lean_object* v_res_2476_; 
v_canonical_boxed_2475_ = lean_unbox(v_canonical_2474_);
v_res_2476_ = l_Lean_mkIdentFrom(v_src_2472_, v_val_2473_, v_canonical_boxed_2475_);
lean_dec(v_src_2472_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom(lean_object* v_src_2492_, lean_object* v_text_2493_, uint8_t v_canonical_2494_){
_start:
{
lean_object* v_info_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v_body_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v_info_2495_ = l_Lean_SourceInfo_fromRef(v_src_2492_, v_canonical_2494_);
v___x_2496_ = lean_box(2);
v___x_2497_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__2));
lean_inc_n(v_info_2495_, 2);
v___x_2498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2498_, 0, v_info_2495_);
lean_ctor_set(v___x_2498_, 1, v_text_2493_);
v___x_2499_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__3));
v___x_2500_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2500_, 0, v_info_2495_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = lean_unsigned_to_nat(2u);
v___x_2502_ = lean_mk_empty_array_with_capacity(v___x_2501_);
lean_inc_ref(v___x_2502_);
v___x_2503_ = lean_array_push(v___x_2502_, v___x_2498_);
v___x_2504_ = lean_array_push(v___x_2503_, v___x_2500_);
v_body_2505_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_body_2505_, 0, v___x_2496_);
lean_ctor_set(v_body_2505_, 1, v___x_2497_);
lean_ctor_set(v_body_2505_, 2, v___x_2504_);
v___x_2506_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__5));
v___x_2507_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__6));
v___x_2508_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2508_, 0, v_info_2495_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = lean_array_push(v___x_2502_, v___x_2508_);
v___x_2510_ = lean_array_push(v___x_2509_, v_body_2505_);
v___x_2511_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2496_);
lean_ctor_set(v___x_2511_, 1, v___x_2506_);
lean_ctor_set(v___x_2511_, 2, v___x_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom___boxed(lean_object* v_src_2512_, lean_object* v_text_2513_, lean_object* v_canonical_2514_){
_start:
{
uint8_t v_canonical_boxed_2515_; lean_object* v_res_2516_; 
v_canonical_boxed_2515_ = lean_unbox(v_canonical_2514_);
v_res_2516_ = l_Lean_mkMarkdownDocCommentFrom(v_src_2512_, v_text_2513_, v_canonical_boxed_2515_);
lean_dec(v_src_2512_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocComment(lean_object* v_text_2517_){
_start:
{
lean_object* v___x_2518_; uint8_t v___x_2519_; lean_object* v___x_2520_; 
v___x_2518_ = lean_box(0);
v___x_2519_ = 0;
v___x_2520_ = l_Lean_mkMarkdownDocCommentFrom(v___x_2518_, v_text_2517_, v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object* v_val_2521_, uint8_t v_canonical_2522_, lean_object* v_toPure_2523_, lean_object* v_____do__lift_2524_){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = l_Lean_mkIdentFrom(v_____do__lift_2524_, v_val_2521_, v_canonical_2522_);
v___x_2526_ = lean_apply_2(v_toPure_2523_, lean_box(0), v___x_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object* v_val_2527_, lean_object* v_canonical_2528_, lean_object* v_toPure_2529_, lean_object* v_____do__lift_2530_){
_start:
{
uint8_t v_canonical_boxed_2531_; lean_object* v_res_2532_; 
v_canonical_boxed_2531_ = lean_unbox(v_canonical_2528_);
v_res_2532_ = l_Lean_mkIdentFromRef___redArg___lam__0(v_val_2527_, v_canonical_boxed_2531_, v_toPure_2529_, v_____do__lift_2530_);
lean_dec(v_____do__lift_2530_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object* v_inst_2533_, lean_object* v_inst_2534_, lean_object* v_val_2535_, uint8_t v_canonical_2536_){
_start:
{
lean_object* v_toApplicative_2537_; lean_object* v_toBind_2538_; lean_object* v_getRef_2539_; lean_object* v_toPure_2540_; lean_object* v___x_2541_; lean_object* v___f_2542_; lean_object* v___x_2543_; 
v_toApplicative_2537_ = lean_ctor_get(v_inst_2533_, 0);
lean_inc_ref(v_toApplicative_2537_);
v_toBind_2538_ = lean_ctor_get(v_inst_2533_, 1);
lean_inc(v_toBind_2538_);
lean_dec_ref(v_inst_2533_);
v_getRef_2539_ = lean_ctor_get(v_inst_2534_, 0);
lean_inc(v_getRef_2539_);
lean_dec_ref(v_inst_2534_);
v_toPure_2540_ = lean_ctor_get(v_toApplicative_2537_, 1);
lean_inc(v_toPure_2540_);
lean_dec_ref(v_toApplicative_2537_);
v___x_2541_ = lean_box(v_canonical_2536_);
v___f_2542_ = lean_alloc_closure((void*)(l_Lean_mkIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2542_, 0, v_val_2535_);
lean_closure_set(v___f_2542_, 1, v___x_2541_);
lean_closure_set(v___f_2542_, 2, v_toPure_2540_);
v___x_2543_ = lean_apply_4(v_toBind_2538_, lean_box(0), lean_box(0), v_getRef_2539_, v___f_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object* v_inst_2544_, lean_object* v_inst_2545_, lean_object* v_val_2546_, lean_object* v_canonical_2547_){
_start:
{
uint8_t v_canonical_boxed_2548_; lean_object* v_res_2549_; 
v_canonical_boxed_2548_ = lean_unbox(v_canonical_2547_);
v_res_2549_ = l_Lean_mkIdentFromRef___redArg(v_inst_2544_, v_inst_2545_, v_val_2546_, v_canonical_boxed_2548_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object* v_m_2550_, lean_object* v_inst_2551_, lean_object* v_inst_2552_, lean_object* v_val_2553_, uint8_t v_canonical_2554_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_mkIdentFromRef___redArg(v_inst_2551_, v_inst_2552_, v_val_2553_, v_canonical_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object* v_m_2556_, lean_object* v_inst_2557_, lean_object* v_inst_2558_, lean_object* v_val_2559_, lean_object* v_canonical_2560_){
_start:
{
uint8_t v_canonical_boxed_2561_; lean_object* v_res_2562_; 
v_canonical_boxed_2561_ = lean_unbox(v_canonical_2560_);
v_res_2562_ = l_Lean_mkIdentFromRef(v_m_2556_, v_inst_2557_, v_inst_2558_, v_val_2559_, v_canonical_boxed_2561_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object* v_src_2566_, lean_object* v_c_2567_, uint8_t v_canonical_2568_){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v_id_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2569_ = ((lean_object*)(l_Lean_mkCIdentFrom___closed__1));
v___x_2570_ = lean_unsigned_to_nat(0u);
lean_inc(v_c_2567_);
v_id_2571_ = l_Lean_addMacroScope(v___x_2569_, v_c_2567_, v___x_2570_);
v___x_2572_ = l_Lean_SourceInfo_fromRef(v_src_2566_, v_canonical_2568_);
v___x_2573_ = 1;
lean_inc(v_id_2571_);
v___x_2574_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_id_2571_, v___x_2573_);
v___x_2575_ = lean_string_utf8_byte_size(v___x_2574_);
v___x_2576_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2574_);
lean_ctor_set(v___x_2576_, 1, v___x_2570_);
lean_ctor_set(v___x_2576_, 2, v___x_2575_);
v___x_2577_ = lean_box(0);
v___x_2578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2578_, 0, v_c_2567_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
lean_ctor_set(v___x_2579_, 1, v___x_2577_);
v___x_2580_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2572_);
lean_ctor_set(v___x_2580_, 1, v___x_2576_);
lean_ctor_set(v___x_2580_, 2, v_id_2571_);
lean_ctor_set(v___x_2580_, 3, v___x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* v_src_2581_, lean_object* v_c_2582_, lean_object* v_canonical_2583_){
_start:
{
uint8_t v_canonical_boxed_2584_; lean_object* v_res_2585_; 
v_canonical_boxed_2584_ = lean_unbox(v_canonical_2583_);
v_res_2585_ = l_Lean_mkCIdentFrom(v_src_2581_, v_c_2582_, v_canonical_boxed_2584_);
lean_dec(v_src_2581_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object* v_c_2586_, uint8_t v_canonical_2587_, lean_object* v_toPure_2588_, lean_object* v_____do__lift_2589_){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = l_Lean_mkCIdentFrom(v_____do__lift_2589_, v_c_2586_, v_canonical_2587_);
v___x_2591_ = lean_apply_2(v_toPure_2588_, lean_box(0), v___x_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object* v_c_2592_, lean_object* v_canonical_2593_, lean_object* v_toPure_2594_, lean_object* v_____do__lift_2595_){
_start:
{
uint8_t v_canonical_boxed_2596_; lean_object* v_res_2597_; 
v_canonical_boxed_2596_ = lean_unbox(v_canonical_2593_);
v_res_2597_ = l_Lean_mkCIdentFromRef___redArg___lam__0(v_c_2592_, v_canonical_boxed_2596_, v_toPure_2594_, v_____do__lift_2595_);
lean_dec(v_____do__lift_2595_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object* v_inst_2598_, lean_object* v_inst_2599_, lean_object* v_c_2600_, uint8_t v_canonical_2601_){
_start:
{
lean_object* v_toApplicative_2602_; lean_object* v_toBind_2603_; lean_object* v_getRef_2604_; lean_object* v_toPure_2605_; lean_object* v___x_2606_; lean_object* v___f_2607_; lean_object* v___x_2608_; 
v_toApplicative_2602_ = lean_ctor_get(v_inst_2598_, 0);
lean_inc_ref(v_toApplicative_2602_);
v_toBind_2603_ = lean_ctor_get(v_inst_2598_, 1);
lean_inc(v_toBind_2603_);
lean_dec_ref(v_inst_2598_);
v_getRef_2604_ = lean_ctor_get(v_inst_2599_, 0);
lean_inc(v_getRef_2604_);
lean_dec_ref(v_inst_2599_);
v_toPure_2605_ = lean_ctor_get(v_toApplicative_2602_, 1);
lean_inc(v_toPure_2605_);
lean_dec_ref(v_toApplicative_2602_);
v___x_2606_ = lean_box(v_canonical_2601_);
v___f_2607_ = lean_alloc_closure((void*)(l_Lean_mkCIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2607_, 0, v_c_2600_);
lean_closure_set(v___f_2607_, 1, v___x_2606_);
lean_closure_set(v___f_2607_, 2, v_toPure_2605_);
v___x_2608_ = lean_apply_4(v_toBind_2603_, lean_box(0), lean_box(0), v_getRef_2604_, v___f_2607_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object* v_inst_2609_, lean_object* v_inst_2610_, lean_object* v_c_2611_, lean_object* v_canonical_2612_){
_start:
{
uint8_t v_canonical_boxed_2613_; lean_object* v_res_2614_; 
v_canonical_boxed_2613_ = lean_unbox(v_canonical_2612_);
v_res_2614_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2609_, v_inst_2610_, v_c_2611_, v_canonical_boxed_2613_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object* v_m_2615_, lean_object* v_inst_2616_, lean_object* v_inst_2617_, lean_object* v_c_2618_, uint8_t v_canonical_2619_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2616_, v_inst_2617_, v_c_2618_, v_canonical_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object* v_m_2621_, lean_object* v_inst_2622_, lean_object* v_inst_2623_, lean_object* v_c_2624_, lean_object* v_canonical_2625_){
_start:
{
uint8_t v_canonical_boxed_2626_; lean_object* v_res_2627_; 
v_canonical_boxed_2626_ = lean_unbox(v_canonical_2625_);
v_res_2627_ = l_Lean_mkCIdentFromRef(v_m_2621_, v_inst_2622_, v_inst_2623_, v_c_2624_, v_canonical_boxed_2626_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object* v_c_2628_){
_start:
{
lean_object* v___x_2629_; uint8_t v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = lean_box(0);
v___x_2630_ = 0;
v___x_2631_ = l_Lean_mkCIdentFrom(v___x_2629_, v_c_2628_, v___x_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdent(lean_object* v_val_2632_){
_start:
{
lean_object* v___x_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2633_ = lean_box(2);
v___x_2634_ = 1;
lean_inc(v_val_2632_);
v___x_2635_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2632_, v___x_2634_);
v___x_2636_ = lean_unsigned_to_nat(0u);
v___x_2637_ = lean_string_utf8_byte_size(v___x_2635_);
v___x_2638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2635_);
lean_ctor_set(v___x_2638_, 1, v___x_2636_);
lean_ctor_set(v___x_2638_, 2, v___x_2637_);
v___x_2639_ = lean_box(0);
v___x_2640_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2633_);
lean_ctor_set(v___x_2640_, 1, v___x_2638_);
lean_ctor_set(v___x_2640_, 2, v_val_2632_);
lean_ctor_set(v___x_2640_, 3, v___x_2639_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object* v_args_2644_){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2645_ = ((lean_object*)(l_Lean_mkGroupNode___closed__1));
v___x_2646_ = lean_box(2);
v___x_2647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
lean_ctor_set(v___x_2647_, 1, v___x_2645_);
lean_ctor_set(v___x_2647_, 2, v_args_2644_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object* v_sep_2648_, lean_object* v_as_2649_, size_t v_sz_2650_, size_t v_i_2651_, lean_object* v_b_2652_){
_start:
{
uint8_t v___x_2653_; 
v___x_2653_ = lean_usize_dec_lt(v_i_2651_, v_sz_2650_);
if (v___x_2653_ == 0)
{
lean_dec(v_sep_2648_);
return v_b_2652_;
}
else
{
lean_object* v_fst_2654_; lean_object* v_snd_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2675_; 
v_fst_2654_ = lean_ctor_get(v_b_2652_, 0);
v_snd_2655_ = lean_ctor_get(v_b_2652_, 1);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_b_2652_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2657_ = v_b_2652_;
v_isShared_2658_ = v_isSharedCheck_2675_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_snd_2655_);
lean_inc(v_fst_2654_);
lean_dec(v_b_2652_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2675_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_r_2660_; lean_object* v_i_2669_; lean_object* v_a_2670_; uint8_t v___x_2671_; 
v_i_2669_ = lean_unsigned_to_nat(0u);
v_a_2670_ = lean_array_uget_borrowed(v_as_2649_, v_i_2651_);
v___x_2671_ = lean_nat_dec_lt(v_i_2669_, v_fst_2654_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; 
lean_inc(v_a_2670_);
v___x_2672_ = lean_array_push(v_snd_2655_, v_a_2670_);
v_r_2660_ = v___x_2672_;
goto v___jp_2659_;
}
else
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_inc(v_sep_2648_);
v___x_2673_ = lean_array_push(v_snd_2655_, v_sep_2648_);
lean_inc(v_a_2670_);
v___x_2674_ = lean_array_push(v___x_2673_, v_a_2670_);
v_r_2660_ = v___x_2674_;
goto v___jp_2659_;
}
v___jp_2659_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2661_ = lean_unsigned_to_nat(1u);
v___x_2662_ = lean_nat_add(v_fst_2654_, v___x_2661_);
lean_dec(v_fst_2654_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 1, v_r_2660_);
lean_ctor_set(v___x_2657_, 0, v___x_2662_);
v___x_2664_ = v___x_2657_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_r_2660_);
v___x_2664_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
size_t v___x_2665_; size_t v___x_2666_; 
v___x_2665_ = ((size_t)1ULL);
v___x_2666_ = lean_usize_add(v_i_2651_, v___x_2665_);
v_i_2651_ = v___x_2666_;
v_b_2652_ = v___x_2664_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object* v_sep_2676_, lean_object* v_as_2677_, lean_object* v_sz_2678_, lean_object* v_i_2679_, lean_object* v_b_2680_){
_start:
{
size_t v_sz_boxed_2681_; size_t v_i_boxed_2682_; lean_object* v_res_2683_; 
v_sz_boxed_2681_ = lean_unbox_usize(v_sz_2678_);
lean_dec(v_sz_2678_);
v_i_boxed_2682_ = lean_unbox_usize(v_i_2679_);
lean_dec(v_i_2679_);
v_res_2683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2676_, v_as_2677_, v_sz_boxed_2681_, v_i_boxed_2682_, v_b_2680_);
lean_dec_ref(v_as_2677_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object* v_as_2689_, lean_object* v_sep_2690_){
_start:
{
lean_object* v___x_2691_; size_t v_sz_2692_; size_t v___x_2693_; lean_object* v___x_2694_; lean_object* v_snd_2695_; 
v___x_2691_ = ((lean_object*)(l_Lean_mkSepArray___closed__1));
v_sz_2692_ = lean_array_size(v_as_2689_);
v___x_2693_ = ((size_t)0ULL);
v___x_2694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2690_, v_as_2689_, v_sz_2692_, v___x_2693_, v___x_2691_);
v_snd_2695_ = lean_ctor_get(v___x_2694_, 1);
lean_inc(v_snd_2695_);
lean_dec_ref(v___x_2694_);
return v_snd_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object* v_as_2696_, lean_object* v_sep_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_mkSepArray(v_as_2696_, v_sep_2697_);
lean_dec_ref(v_as_2696_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object* v_arg_2706_){
_start:
{
if (lean_obj_tag(v_arg_2706_) == 0)
{
lean_object* v___x_2707_; 
v___x_2707_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
return v___x_2707_;
}
else
{
lean_object* v_val_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_val_2708_ = lean_ctor_get(v_arg_2706_, 0);
lean_inc(v_val_2708_);
lean_dec_ref_known(v_arg_2706_, 1);
v___x_2709_ = lean_unsigned_to_nat(1u);
v___x_2710_ = lean_mk_empty_array_with_capacity(v___x_2709_);
v___x_2711_ = lean_array_push(v___x_2710_, v_val_2708_);
v___x_2712_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2713_ = lean_box(2);
v___x_2714_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
lean_ctor_set(v___x_2714_, 1, v___x_2712_);
lean_ctor_set(v___x_2714_, 2, v___x_2711_);
return v___x_2714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object* v_ref_2721_, uint8_t v_canonical_2722_){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2723_ = ((lean_object*)(l_Lean_mkHole___closed__1));
v___x_2724_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_2725_ = l_Lean_mkAtomFrom(v_ref_2721_, v___x_2724_, v_canonical_2722_);
v___x_2726_ = lean_unsigned_to_nat(1u);
v___x_2727_ = lean_mk_empty_array_with_capacity(v___x_2726_);
v___x_2728_ = lean_array_push(v___x_2727_, v___x_2725_);
v___x_2729_ = lean_box(2);
v___x_2730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
lean_ctor_set(v___x_2730_, 1, v___x_2723_);
lean_ctor_set(v___x_2730_, 2, v___x_2728_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object* v_ref_2731_, lean_object* v_canonical_2732_){
_start:
{
uint8_t v_canonical_boxed_2733_; lean_object* v_res_2734_; 
v_canonical_boxed_2733_ = lean_unbox(v_canonical_2732_);
v_res_2734_ = l_Lean_mkHole(v_ref_2731_, v_canonical_boxed_2733_);
lean_dec(v_ref_2731_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object* v_a_2735_, lean_object* v_sep_2736_){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2737_ = l_Lean_mkSepArray(v_a_2735_, v_sep_2736_);
v___x_2738_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2739_ = lean_box(2);
v___x_2740_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
lean_ctor_set(v___x_2740_, 1, v___x_2738_);
lean_ctor_set(v___x_2740_, 2, v___x_2737_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object* v_a_2741_, lean_object* v_sep_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_Syntax_mkSep(v_a_2741_, v_sep_2742_);
lean_dec_ref(v_a_2741_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object* v_sep_2750_, lean_object* v_elems_2751_){
_start:
{
uint8_t v___x_2752_; 
lean_inc_ref(v_sep_2750_);
v___x_2752_ = lean_string_isempty(v_sep_2750_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = l_Lean_mkAtom(v_sep_2750_);
v___x_2754_ = l_Lean_mkSepArray(v_elems_2751_, v___x_2753_);
return v___x_2754_;
}
else
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
lean_dec_ref(v_sep_2750_);
v___x_2755_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___x_2756_ = l_Lean_mkSepArray(v_elems_2751_, v___x_2755_);
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object* v_sep_2757_, lean_object* v_elems_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2757_, v_elems_2758_);
lean_dec_ref(v_elems_2758_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object* v_elems_2760_, lean_object* v_toPure_2761_, lean_object* v_sep_2762_, lean_object* v_ref_2763_){
_start:
{
lean_object* v___y_2765_; uint8_t v___x_2768_; 
lean_inc_ref(v_sep_2762_);
v___x_2768_ = lean_string_isempty(v_sep_2762_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_mkAtomFrom(v_ref_2763_, v_sep_2762_, v___x_2768_);
v___y_2765_ = v___x_2769_;
goto v___jp_2764_;
}
else
{
lean_object* v___x_2770_; 
lean_dec_ref(v_sep_2762_);
v___x_2770_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___y_2765_ = v___x_2770_;
goto v___jp_2764_;
}
v___jp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = l_Lean_mkSepArray(v_elems_2760_, v___y_2765_);
v___x_2767_ = lean_apply_2(v_toPure_2761_, lean_box(0), v___x_2766_);
return v___x_2767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object* v_elems_2771_, lean_object* v_toPure_2772_, lean_object* v_sep_2773_, lean_object* v_ref_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(v_elems_2771_, v_toPure_2772_, v_sep_2773_, v_ref_2774_);
lean_dec(v_ref_2774_);
lean_dec_ref(v_elems_2771_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object* v_inst_2776_, lean_object* v_inst_2777_, lean_object* v_sep_2778_, lean_object* v_elems_2779_){
_start:
{
lean_object* v_toApplicative_2780_; lean_object* v_toBind_2781_; lean_object* v_getRef_2782_; lean_object* v_toPure_2783_; lean_object* v___f_2784_; lean_object* v___x_2785_; 
v_toApplicative_2780_ = lean_ctor_get(v_inst_2776_, 0);
lean_inc_ref(v_toApplicative_2780_);
v_toBind_2781_ = lean_ctor_get(v_inst_2776_, 1);
lean_inc(v_toBind_2781_);
lean_dec_ref(v_inst_2776_);
v_getRef_2782_ = lean_ctor_get(v_inst_2777_, 0);
lean_inc(v_getRef_2782_);
lean_dec_ref(v_inst_2777_);
v_toPure_2783_ = lean_ctor_get(v_toApplicative_2780_, 1);
lean_inc(v_toPure_2783_);
lean_dec_ref(v_toApplicative_2780_);
v___f_2784_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2784_, 0, v_elems_2779_);
lean_closure_set(v___f_2784_, 1, v_toPure_2783_);
lean_closure_set(v___f_2784_, 2, v_sep_2778_);
v___x_2785_ = lean_apply_4(v_toBind_2781_, lean_box(0), lean_box(0), v_getRef_2782_, v___f_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object* v_m_2786_, lean_object* v_inst_2787_, lean_object* v_inst_2788_, lean_object* v_sep_2789_, lean_object* v_elems_2790_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(v_inst_2787_, v_inst_2788_, v_sep_2789_, v_elems_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* v_sep_2792_, lean_object* v_elems_2793_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2792_, v_elems_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* v_sep_2795_, lean_object* v_elems_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_Syntax_TSepArray_ofElems___redArg(v_sep_2795_, v_elems_2796_);
lean_dec_ref(v_elems_2796_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* v_k_2798_, lean_object* v_sep_2799_, lean_object* v_elems_2800_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2799_, v_elems_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* v_k_2802_, lean_object* v_sep_2803_, lean_object* v_elems_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_Syntax_TSepArray_ofElems(v_k_2802_, v_sep_2803_, v_elems_2804_);
lean_dec_ref(v_elems_2804_);
lean_dec(v_k_2802_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* v_k_2806_, lean_object* v_sep_2807_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(v___x_2808_, 0, v_k_2806_);
lean_closure_set(v___x_2808_, 1, v_sep_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* v_fn_2815_, lean_object* v_x_2816_){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v___x_2817_ = lean_array_get_size(v_x_2816_);
v___x_2818_ = lean_unsigned_to_nat(0u);
v___x_2819_ = lean_nat_dec_eq(v___x_2817_, v___x_2818_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2820_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_2821_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2822_ = lean_box(2);
v___x_2823_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
lean_ctor_set(v___x_2823_, 1, v___x_2821_);
lean_ctor_set(v___x_2823_, 2, v_x_2816_);
v___x_2824_ = lean_unsigned_to_nat(2u);
v___x_2825_ = lean_mk_empty_array_with_capacity(v___x_2824_);
v___x_2826_ = lean_array_push(v___x_2825_, v_fn_2815_);
v___x_2827_ = lean_array_push(v___x_2826_, v___x_2823_);
v___x_2828_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2822_);
lean_ctor_set(v___x_2828_, 1, v___x_2820_);
lean_ctor_set(v___x_2828_, 2, v___x_2827_);
return v___x_2828_;
}
else
{
lean_dec_ref(v_x_2816_);
return v_fn_2815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* v_fn_2829_, lean_object* v_args_2830_){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = l_Lean_mkCIdent(v_fn_2829_);
v___x_2832_ = l_Lean_Syntax_mkApp(v___x_2831_, v_args_2830_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* v_kind_2833_, lean_object* v_val_2834_, lean_object* v_info_2835_){
_start:
{
lean_object* v_atom_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v_atom_2836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2836_, 0, v_info_2835_);
lean_ctor_set(v_atom_2836_, 1, v_val_2834_);
v___x_2837_ = lean_unsigned_to_nat(1u);
v___x_2838_ = lean_mk_empty_array_with_capacity(v___x_2837_);
v___x_2839_ = lean_array_push(v___x_2838_, v_atom_2836_);
v___x_2840_ = lean_box(2);
v___x_2841_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
lean_ctor_set(v___x_2841_, 1, v_kind_2833_);
lean_ctor_set(v___x_2841_, 2, v___x_2839_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t v_val_2845_, lean_object* v_info_2846_){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_2848_ = l_Char_quote(v_val_2845_);
v___x_2849_ = l_Lean_Syntax_mkLit(v___x_2847_, v___x_2848_, v_info_2846_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* v_val_2850_, lean_object* v_info_2851_){
_start:
{
uint32_t v_val_boxed_2852_; lean_object* v_res_2853_; 
v_val_boxed_2852_ = lean_unbox_uint32(v_val_2850_);
lean_dec(v_val_2850_);
v_res_2853_ = l_Lean_Syntax_mkCharLit(v_val_boxed_2852_, v_info_2851_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* v_val_2857_, lean_object* v_info_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_2860_ = l_String_quote(v_val_2857_);
v___x_2861_ = l_Lean_Syntax_mkLit(v___x_2859_, v___x_2860_, v_info_2858_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* v_val_2865_, lean_object* v_info_2866_){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2868_ = l_Lean_Syntax_mkLit(v___x_2867_, v_val_2865_, v_info_2866_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* v_val_2869_, lean_object* v_info_2870_){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2872_ = l_Nat_reprFast(v_val_2869_);
v___x_2873_ = l_Lean_Syntax_mkLit(v___x_2871_, v___x_2872_, v_info_2870_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* v_val_2877_, lean_object* v_info_2878_){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_2880_ = l_Lean_Syntax_mkLit(v___x_2879_, v_val_2877_, v_info_2878_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* v_val_2884_, lean_object* v_info_2885_){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_2887_ = l_Lean_Syntax_mkLit(v___x_2886_, v_val_2884_, v_info_2885_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* v_s_2888_, lean_object* v_i_2889_, lean_object* v_val_2890_){
_start:
{
uint8_t v___x_2891_; 
v___x_2891_ = lean_string_utf8_at_end(v_s_2888_, v_i_2889_);
if (v___x_2891_ == 0)
{
uint32_t v_c_2892_; uint32_t v___x_2893_; uint8_t v___x_2894_; 
v_c_2892_ = lean_string_utf8_get(v_s_2888_, v_i_2889_);
v___x_2893_ = 48;
v___x_2894_ = lean_uint32_dec_eq(v_c_2892_, v___x_2893_);
if (v___x_2894_ == 0)
{
uint32_t v___x_2895_; uint8_t v___x_2896_; 
v___x_2895_ = 49;
v___x_2896_ = lean_uint32_dec_eq(v_c_2892_, v___x_2895_);
if (v___x_2896_ == 0)
{
uint32_t v___x_2897_; uint8_t v___x_2898_; 
v___x_2897_ = 95;
v___x_2898_ = lean_uint32_dec_eq(v_c_2892_, v___x_2897_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; 
lean_dec(v_val_2890_);
lean_dec(v_i_2889_);
v___x_2899_ = lean_box(0);
return v___x_2899_;
}
else
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_string_utf8_next(v_s_2888_, v_i_2889_);
lean_dec(v_i_2889_);
v_i_2889_ = v___x_2900_;
goto _start;
}
}
else
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2902_ = lean_string_utf8_next(v_s_2888_, v_i_2889_);
lean_dec(v_i_2889_);
v___x_2903_ = lean_unsigned_to_nat(2u);
v___x_2904_ = lean_nat_mul(v___x_2903_, v_val_2890_);
lean_dec(v_val_2890_);
v___x_2905_ = lean_unsigned_to_nat(1u);
v___x_2906_ = lean_nat_add(v___x_2904_, v___x_2905_);
lean_dec(v___x_2904_);
v_i_2889_ = v___x_2902_;
v_val_2890_ = v___x_2906_;
goto _start;
}
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2908_ = lean_string_utf8_next(v_s_2888_, v_i_2889_);
lean_dec(v_i_2889_);
v___x_2909_ = lean_unsigned_to_nat(2u);
v___x_2910_ = lean_nat_mul(v___x_2909_, v_val_2890_);
lean_dec(v_val_2890_);
v_i_2889_ = v___x_2908_;
v_val_2890_ = v___x_2910_;
goto _start;
}
}
else
{
lean_object* v___x_2912_; 
lean_dec(v_i_2889_);
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_val_2890_);
return v___x_2912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* v_s_2913_, lean_object* v_i_2914_, lean_object* v_val_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2913_, v_i_2914_, v_val_2915_);
lean_dec_ref(v_s_2913_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* v_s_2917_, lean_object* v_i_2918_, lean_object* v_val_2919_){
_start:
{
uint8_t v___x_2920_; 
v___x_2920_ = lean_string_utf8_at_end(v_s_2917_, v_i_2918_);
if (v___x_2920_ == 0)
{
uint32_t v_c_2921_; uint8_t v___y_2923_; uint32_t v___x_2937_; uint8_t v___x_2938_; 
v_c_2921_ = lean_string_utf8_get(v_s_2917_, v_i_2918_);
v___x_2937_ = 48;
v___x_2938_ = lean_uint32_dec_le(v___x_2937_, v_c_2921_);
if (v___x_2938_ == 0)
{
v___y_2923_ = v___x_2920_;
goto v___jp_2922_;
}
else
{
uint32_t v___x_2939_; uint8_t v___x_2940_; 
v___x_2939_ = 55;
v___x_2940_ = lean_uint32_dec_le(v_c_2921_, v___x_2939_);
v___y_2923_ = v___x_2940_;
goto v___jp_2922_;
}
v___jp_2922_:
{
if (v___y_2923_ == 0)
{
uint32_t v___x_2924_; uint8_t v___x_2925_; 
v___x_2924_ = 95;
v___x_2925_ = lean_uint32_dec_eq(v_c_2921_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; 
lean_dec(v_val_2919_);
lean_dec(v_i_2918_);
v___x_2926_ = lean_box(0);
return v___x_2926_;
}
else
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_string_utf8_next(v_s_2917_, v_i_2918_);
lean_dec(v_i_2918_);
v_i_2918_ = v___x_2927_;
goto _start;
}
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2929_ = lean_string_utf8_next(v_s_2917_, v_i_2918_);
lean_dec(v_i_2918_);
v___x_2930_ = lean_unsigned_to_nat(8u);
v___x_2931_ = lean_nat_mul(v___x_2930_, v_val_2919_);
lean_dec(v_val_2919_);
v___x_2932_ = lean_uint32_to_nat(v_c_2921_);
v___x_2933_ = lean_nat_add(v___x_2931_, v___x_2932_);
lean_dec(v___x_2932_);
lean_dec(v___x_2931_);
v___x_2934_ = lean_unsigned_to_nat(48u);
v___x_2935_ = lean_nat_sub(v___x_2933_, v___x_2934_);
lean_dec(v___x_2933_);
v_i_2918_ = v___x_2929_;
v_val_2919_ = v___x_2935_;
goto _start;
}
}
}
else
{
lean_object* v___x_2941_; 
lean_dec(v_i_2918_);
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v_val_2919_);
return v___x_2941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* v_s_2942_, lean_object* v_i_2943_, lean_object* v_val_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2942_, v_i_2943_, v_val_2944_);
lean_dec_ref(v_s_2942_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object* v_s_2946_, lean_object* v_i_2947_){
_start:
{
uint32_t v_c_2948_; lean_object* v_i_2949_; uint32_t v___x_2976_; uint8_t v___x_2977_; 
v_c_2948_ = lean_string_utf8_get(v_s_2946_, v_i_2947_);
v_i_2949_ = lean_string_utf8_next(v_s_2946_, v_i_2947_);
v___x_2976_ = 48;
v___x_2977_ = lean_uint32_dec_le(v___x_2976_, v_c_2948_);
if (v___x_2977_ == 0)
{
goto v___jp_2964_;
}
else
{
uint32_t v___x_2978_; uint8_t v___x_2979_; 
v___x_2978_ = 57;
v___x_2979_ = lean_uint32_dec_le(v_c_2948_, v___x_2978_);
if (v___x_2979_ == 0)
{
goto v___jp_2964_;
}
else
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2980_ = lean_uint32_to_nat(v_c_2948_);
v___x_2981_ = lean_unsigned_to_nat(48u);
v___x_2982_ = lean_nat_sub(v___x_2980_, v___x_2981_);
lean_dec(v___x_2980_);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
lean_ctor_set(v___x_2983_, 1, v_i_2949_);
v___x_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
return v___x_2984_;
}
}
v___jp_2950_:
{
uint32_t v___x_2951_; uint8_t v___x_2952_; 
v___x_2951_ = 65;
v___x_2952_ = lean_uint32_dec_le(v___x_2951_, v_c_2948_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; 
lean_dec(v_i_2949_);
v___x_2953_ = lean_box(0);
return v___x_2953_;
}
else
{
uint32_t v___x_2954_; uint8_t v___x_2955_; 
v___x_2954_ = 70;
v___x_2955_ = lean_uint32_dec_le(v_c_2948_, v___x_2954_);
if (v___x_2955_ == 0)
{
lean_object* v___x_2956_; 
lean_dec(v_i_2949_);
v___x_2956_ = lean_box(0);
return v___x_2956_;
}
else
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2957_ = lean_unsigned_to_nat(10u);
v___x_2958_ = lean_uint32_to_nat(v_c_2948_);
v___x_2959_ = lean_nat_add(v___x_2957_, v___x_2958_);
lean_dec(v___x_2958_);
v___x_2960_ = lean_unsigned_to_nat(65u);
v___x_2961_ = lean_nat_sub(v___x_2959_, v___x_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
lean_ctor_set(v___x_2962_, 1, v_i_2949_);
v___x_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
return v___x_2963_;
}
}
}
v___jp_2964_:
{
uint32_t v___x_2965_; uint8_t v___x_2966_; 
v___x_2965_ = 97;
v___x_2966_ = lean_uint32_dec_le(v___x_2965_, v_c_2948_);
if (v___x_2966_ == 0)
{
goto v___jp_2950_;
}
else
{
uint32_t v___x_2967_; uint8_t v___x_2968_; 
v___x_2967_ = 102;
v___x_2968_ = lean_uint32_dec_le(v_c_2948_, v___x_2967_);
if (v___x_2968_ == 0)
{
goto v___jp_2950_;
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2969_ = lean_unsigned_to_nat(10u);
v___x_2970_ = lean_uint32_to_nat(v_c_2948_);
v___x_2971_ = lean_nat_add(v___x_2969_, v___x_2970_);
lean_dec(v___x_2970_);
v___x_2972_ = lean_unsigned_to_nat(97u);
v___x_2973_ = lean_nat_sub(v___x_2971_, v___x_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
lean_ctor_set(v___x_2974_, 1, v_i_2949_);
v___x_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
return v___x_2975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* v_s_2985_, lean_object* v_i_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2985_, v_i_2986_);
lean_dec(v_i_2986_);
lean_dec_ref(v_s_2985_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object* v_s_2988_, lean_object* v_i_2989_, lean_object* v_val_2990_){
_start:
{
uint8_t v___x_2991_; 
v___x_2991_ = lean_string_utf8_at_end(v_s_2988_, v_i_2989_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; 
v___x_2992_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2988_, v_i_2989_);
if (lean_obj_tag(v___x_2992_) == 0)
{
uint32_t v___x_2993_; uint32_t v___x_2994_; uint8_t v___x_2995_; 
v___x_2993_ = lean_string_utf8_get(v_s_2988_, v_i_2989_);
v___x_2994_ = 95;
v___x_2995_ = lean_uint32_dec_eq(v___x_2993_, v___x_2994_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
lean_dec(v_val_2990_);
lean_dec(v_i_2989_);
v___x_2996_ = lean_box(0);
return v___x_2996_;
}
else
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_string_utf8_next(v_s_2988_, v_i_2989_);
lean_dec(v_i_2989_);
v_i_2989_ = v___x_2997_;
goto _start;
}
}
else
{
lean_object* v_val_2999_; lean_object* v_fst_3000_; lean_object* v_snd_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_dec(v_i_2989_);
v_val_2999_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_val_2999_);
lean_dec_ref_known(v___x_2992_, 1);
v_fst_3000_ = lean_ctor_get(v_val_2999_, 0);
lean_inc(v_fst_3000_);
v_snd_3001_ = lean_ctor_get(v_val_2999_, 1);
lean_inc(v_snd_3001_);
lean_dec(v_val_2999_);
v___x_3002_ = lean_unsigned_to_nat(16u);
v___x_3003_ = lean_nat_mul(v___x_3002_, v_val_2990_);
lean_dec(v_val_2990_);
v___x_3004_ = lean_nat_add(v___x_3003_, v_fst_3000_);
lean_dec(v_fst_3000_);
lean_dec(v___x_3003_);
v_i_2989_ = v_snd_3001_;
v_val_2990_ = v___x_3004_;
goto _start;
}
}
else
{
lean_object* v___x_3006_; 
lean_dec(v_i_2989_);
v___x_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3006_, 0, v_val_2990_);
return v___x_3006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* v_s_3007_, lean_object* v_i_3008_, lean_object* v_val_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3007_, v_i_3008_, v_val_3009_);
lean_dec_ref(v_s_3007_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object* v_s_3011_, lean_object* v_i_3012_, lean_object* v_val_3013_){
_start:
{
uint8_t v___x_3014_; 
v___x_3014_ = lean_string_utf8_at_end(v_s_3011_, v_i_3012_);
if (v___x_3014_ == 0)
{
uint32_t v_c_3015_; uint8_t v___y_3017_; uint32_t v___x_3031_; uint8_t v___x_3032_; 
v_c_3015_ = lean_string_utf8_get(v_s_3011_, v_i_3012_);
v___x_3031_ = 48;
v___x_3032_ = lean_uint32_dec_le(v___x_3031_, v_c_3015_);
if (v___x_3032_ == 0)
{
v___y_3017_ = v___x_3014_;
goto v___jp_3016_;
}
else
{
uint32_t v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = 57;
v___x_3034_ = lean_uint32_dec_le(v_c_3015_, v___x_3033_);
v___y_3017_ = v___x_3034_;
goto v___jp_3016_;
}
v___jp_3016_:
{
if (v___y_3017_ == 0)
{
uint32_t v___x_3018_; uint8_t v___x_3019_; 
v___x_3018_ = 95;
v___x_3019_ = lean_uint32_dec_eq(v_c_3015_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; 
lean_dec(v_val_3013_);
lean_dec(v_i_3012_);
v___x_3020_ = lean_box(0);
return v___x_3020_;
}
else
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_string_utf8_next(v_s_3011_, v_i_3012_);
lean_dec(v_i_3012_);
v_i_3012_ = v___x_3021_;
goto _start;
}
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3023_ = lean_string_utf8_next(v_s_3011_, v_i_3012_);
lean_dec(v_i_3012_);
v___x_3024_ = lean_unsigned_to_nat(10u);
v___x_3025_ = lean_nat_mul(v___x_3024_, v_val_3013_);
lean_dec(v_val_3013_);
v___x_3026_ = lean_uint32_to_nat(v_c_3015_);
v___x_3027_ = lean_nat_add(v___x_3025_, v___x_3026_);
lean_dec(v___x_3026_);
lean_dec(v___x_3025_);
v___x_3028_ = lean_unsigned_to_nat(48u);
v___x_3029_ = lean_nat_sub(v___x_3027_, v___x_3028_);
lean_dec(v___x_3027_);
v_i_3012_ = v___x_3023_;
v_val_3013_ = v___x_3029_;
goto _start;
}
}
}
else
{
lean_object* v___x_3035_; 
lean_dec(v_i_3012_);
v___x_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3035_, 0, v_val_3013_);
return v___x_3035_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* v_s_3036_, lean_object* v_i_3037_, lean_object* v_val_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3036_, v_i_3037_, v_val_3038_);
lean_dec_ref(v_s_3036_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* v_s_3042_){
_start:
{
lean_object* v_len_3043_; lean_object* v___x_3044_; uint8_t v___x_3054_; 
v_len_3043_ = lean_string_length(v_s_3042_);
v___x_3044_ = lean_unsigned_to_nat(0u);
v___x_3054_ = lean_nat_dec_eq(v_len_3043_, v___x_3044_);
if (v___x_3054_ == 0)
{
uint32_t v_c_3055_; uint32_t v___x_3056_; uint8_t v___x_3057_; 
v_c_3055_ = lean_string_utf8_get(v_s_3042_, v___x_3044_);
v___x_3056_ = 48;
v___x_3057_ = lean_uint32_dec_eq(v_c_3055_, v___x_3056_);
if (v___x_3057_ == 0)
{
uint8_t v___x_3058_; 
lean_dec(v_len_3043_);
v___x_3058_ = lean_uint32_dec_le(v___x_3056_, v_c_3055_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_box(0);
return v___x_3059_;
}
else
{
uint32_t v___x_3060_; uint8_t v___x_3061_; 
v___x_3060_ = 57;
v___x_3061_ = lean_uint32_dec_le(v_c_3055_, v___x_3060_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; 
v___x_3062_ = lean_box(0);
return v___x_3062_;
}
else
{
lean_object* v___x_3063_; 
v___x_3063_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3042_, v___x_3044_, v___x_3044_);
return v___x_3063_;
}
}
}
else
{
lean_object* v___x_3064_; uint8_t v___x_3065_; 
v___x_3064_ = lean_unsigned_to_nat(1u);
v___x_3065_ = lean_nat_dec_eq(v_len_3043_, v___x_3064_);
lean_dec(v_len_3043_);
if (v___x_3065_ == 0)
{
uint32_t v_c_3066_; uint32_t v___x_3067_; uint8_t v___x_3068_; 
v_c_3066_ = lean_string_utf8_get(v_s_3042_, v___x_3064_);
v___x_3067_ = 120;
v___x_3068_ = lean_uint32_dec_eq(v_c_3066_, v___x_3067_);
if (v___x_3068_ == 0)
{
uint32_t v___x_3069_; uint8_t v___x_3070_; 
v___x_3069_ = 88;
v___x_3070_ = lean_uint32_dec_eq(v_c_3066_, v___x_3069_);
if (v___x_3070_ == 0)
{
uint32_t v___x_3071_; uint8_t v___x_3072_; 
v___x_3071_ = 98;
v___x_3072_ = lean_uint32_dec_eq(v_c_3066_, v___x_3071_);
if (v___x_3072_ == 0)
{
uint32_t v___x_3073_; uint8_t v___x_3074_; 
v___x_3073_ = 66;
v___x_3074_ = lean_uint32_dec_eq(v_c_3066_, v___x_3073_);
if (v___x_3074_ == 0)
{
uint32_t v___x_3075_; uint8_t v___x_3076_; 
v___x_3075_ = 111;
v___x_3076_ = lean_uint32_dec_eq(v_c_3066_, v___x_3075_);
if (v___x_3076_ == 0)
{
uint32_t v___x_3077_; uint8_t v___x_3078_; 
v___x_3077_ = 79;
v___x_3078_ = lean_uint32_dec_eq(v_c_3066_, v___x_3077_);
if (v___x_3078_ == 0)
{
uint8_t v___x_3079_; 
v___x_3079_ = lean_uint32_dec_le(v___x_3056_, v_c_3066_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; 
v___x_3080_ = lean_box(0);
return v___x_3080_;
}
else
{
uint32_t v___x_3081_; uint8_t v___x_3082_; 
v___x_3081_ = 57;
v___x_3082_ = lean_uint32_dec_le(v_c_3066_, v___x_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_box(0);
return v___x_3083_;
}
else
{
lean_object* v___x_3084_; 
v___x_3084_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3042_, v___x_3044_, v___x_3044_);
return v___x_3084_;
}
}
}
else
{
goto v___jp_3045_;
}
}
else
{
goto v___jp_3045_;
}
}
else
{
goto v___jp_3048_;
}
}
else
{
goto v___jp_3048_;
}
}
else
{
goto v___jp_3051_;
}
}
else
{
goto v___jp_3051_;
}
}
else
{
lean_object* v___x_3085_; 
v___x_3085_ = ((lean_object*)(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0));
return v___x_3085_;
}
}
}
else
{
lean_object* v___x_3086_; 
lean_dec(v_len_3043_);
v___x_3086_ = lean_box(0);
return v___x_3086_;
}
v___jp_3045_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_unsigned_to_nat(2u);
v___x_3047_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_3042_, v___x_3046_, v___x_3044_);
return v___x_3047_;
}
v___jp_3048_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = lean_unsigned_to_nat(2u);
v___x_3050_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_3042_, v___x_3049_, v___x_3044_);
return v___x_3050_;
}
v___jp_3051_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = lean_unsigned_to_nat(2u);
v___x_3053_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3042_, v___x_3052_, v___x_3044_);
return v___x_3053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* v_s_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_s_3087_);
lean_dec_ref(v_s_3087_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* v_litKind_3089_, lean_object* v_stx_3090_){
_start:
{
if (lean_obj_tag(v_stx_3090_) == 1)
{
lean_object* v_kind_3091_; lean_object* v_args_3092_; uint8_t v___y_3094_; uint8_t v___x_3101_; 
v_kind_3091_ = lean_ctor_get(v_stx_3090_, 1);
v_args_3092_ = lean_ctor_get(v_stx_3090_, 2);
v___x_3101_ = lean_name_eq(v_kind_3091_, v_litKind_3089_);
if (v___x_3101_ == 0)
{
v___y_3094_ = v___x_3101_;
goto v___jp_3093_;
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; 
v___x_3102_ = lean_array_get_size(v_args_3092_);
v___x_3103_ = lean_unsigned_to_nat(1u);
v___x_3104_ = lean_nat_dec_eq(v___x_3102_, v___x_3103_);
v___y_3094_ = v___x_3104_;
goto v___jp_3093_;
}
v___jp_3093_:
{
if (v___y_3094_ == 0)
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_box(0);
return v___x_3095_;
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = lean_unsigned_to_nat(0u);
v___x_3097_ = lean_array_fget_borrowed(v_args_3092_, v___x_3096_);
if (lean_obj_tag(v___x_3097_) == 2)
{
lean_object* v_val_3098_; lean_object* v___x_3099_; 
v_val_3098_ = lean_ctor_get(v___x_3097_, 1);
lean_inc_ref(v_val_3098_);
v___x_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3099_, 0, v_val_3098_);
return v___x_3099_;
}
else
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_box(0);
return v___x_3100_;
}
}
}
}
else
{
lean_object* v___x_3105_; 
v___x_3105_ = lean_box(0);
return v___x_3105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* v_litKind_3106_, lean_object* v_stx_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_Syntax_isLit_x3f(v_litKind_3106_, v_stx_3107_);
lean_dec(v_stx_3107_);
lean_dec(v_litKind_3106_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object* v_litKind_3109_, lean_object* v_stx_3110_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Lean_Syntax_isLit_x3f(v_litKind_3109_, v_stx_3110_);
if (lean_obj_tag(v___x_3111_) == 1)
{
lean_object* v_val_3112_; lean_object* v___x_3113_; 
v_val_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_val_3112_);
lean_dec_ref_known(v___x_3111_, 1);
v___x_3113_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_val_3112_);
lean_dec(v_val_3112_);
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; 
lean_dec(v___x_3111_);
v___x_3114_ = lean_box(0);
return v___x_3114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object* v_litKind_3115_, lean_object* v_stx_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v_litKind_3115_, v_stx_3116_);
lean_dec(v_stx_3116_);
lean_dec(v_litKind_3115_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* v_s_3118_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_3120_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3119_, v_s_3118_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* v_s_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_Syntax_isNatLit_x3f(v_s_3121_);
lean_dec(v_s_3121_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* v_s_3126_){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = ((lean_object*)(l_Lean_Syntax_isFieldIdx_x3f___closed__1));
v___x_3128_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3127_, v_s_3126_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* v_s_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_Syntax_isFieldIdx_x3f(v_s_3129_);
lean_dec(v_s_3129_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* v_s_3131_, lean_object* v_i_3132_, lean_object* v_val_3133_, lean_object* v_e_3134_, uint8_t v_sign_3135_, lean_object* v_exp_3136_){
_start:
{
uint8_t v___x_3137_; 
v___x_3137_ = lean_string_utf8_at_end(v_s_3131_, v_i_3132_);
if (v___x_3137_ == 0)
{
uint32_t v_c_3138_; uint8_t v___y_3140_; uint32_t v___x_3154_; uint8_t v___x_3155_; 
v_c_3138_ = lean_string_utf8_get(v_s_3131_, v_i_3132_);
v___x_3154_ = 48;
v___x_3155_ = lean_uint32_dec_le(v___x_3154_, v_c_3138_);
if (v___x_3155_ == 0)
{
v___y_3140_ = v___x_3137_;
goto v___jp_3139_;
}
else
{
uint32_t v___x_3156_; uint8_t v___x_3157_; 
v___x_3156_ = 57;
v___x_3157_ = lean_uint32_dec_le(v_c_3138_, v___x_3156_);
v___y_3140_ = v___x_3157_;
goto v___jp_3139_;
}
v___jp_3139_:
{
if (v___y_3140_ == 0)
{
uint32_t v___x_3141_; uint8_t v___x_3142_; 
v___x_3141_ = 95;
v___x_3142_ = lean_uint32_dec_eq(v_c_3138_, v___x_3141_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; 
lean_dec(v_exp_3136_);
lean_dec(v_val_3133_);
lean_dec(v_i_3132_);
v___x_3143_ = lean_box(0);
return v___x_3143_;
}
else
{
lean_object* v___x_3144_; 
v___x_3144_ = lean_string_utf8_next(v_s_3131_, v_i_3132_);
lean_dec(v_i_3132_);
v_i_3132_ = v___x_3144_;
goto _start;
}
}
else
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3146_ = lean_string_utf8_next(v_s_3131_, v_i_3132_);
lean_dec(v_i_3132_);
v___x_3147_ = lean_unsigned_to_nat(10u);
v___x_3148_ = lean_nat_mul(v___x_3147_, v_exp_3136_);
lean_dec(v_exp_3136_);
v___x_3149_ = lean_uint32_to_nat(v_c_3138_);
v___x_3150_ = lean_nat_add(v___x_3148_, v___x_3149_);
lean_dec(v___x_3149_);
lean_dec(v___x_3148_);
v___x_3151_ = lean_unsigned_to_nat(48u);
v___x_3152_ = lean_nat_sub(v___x_3150_, v___x_3151_);
lean_dec(v___x_3150_);
v_i_3132_ = v___x_3146_;
v_exp_3136_ = v___x_3152_;
goto _start;
}
}
}
else
{
lean_dec(v_i_3132_);
if (v_sign_3135_ == 0)
{
uint8_t v___x_3158_; 
v___x_3158_ = lean_nat_dec_le(v_e_3134_, v_exp_3136_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3159_ = lean_nat_sub(v_e_3134_, v_exp_3136_);
lean_dec(v_exp_3136_);
v___x_3160_ = lean_box(v___x_3137_);
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
lean_ctor_set(v___x_3161_, 1, v___x_3159_);
v___x_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3162_, 0, v_val_3133_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3164_ = lean_nat_sub(v_exp_3136_, v_e_3134_);
lean_dec(v_exp_3136_);
v___x_3165_ = lean_box(v_sign_3135_);
v___x_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3164_);
v___x_3167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3167_, 0, v_val_3133_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
return v___x_3168_;
}
}
else
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3169_ = lean_nat_add(v_exp_3136_, v_e_3134_);
lean_dec(v_exp_3136_);
v___x_3170_ = lean_box(v_sign_3135_);
v___x_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
lean_ctor_set(v___x_3171_, 1, v___x_3169_);
v___x_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3172_, 0, v_val_3133_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
return v___x_3173_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* v_s_3174_, lean_object* v_i_3175_, lean_object* v_val_3176_, lean_object* v_e_3177_, lean_object* v_sign_3178_, lean_object* v_exp_3179_){
_start:
{
uint8_t v_sign_boxed_3180_; lean_object* v_res_3181_; 
v_sign_boxed_3180_ = lean_unbox(v_sign_3178_);
v_res_3181_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3174_, v_i_3175_, v_val_3176_, v_e_3177_, v_sign_boxed_3180_, v_exp_3179_);
lean_dec(v_e_3177_);
lean_dec_ref(v_s_3174_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* v_s_3182_, lean_object* v_i_3183_, lean_object* v_val_3184_, lean_object* v_e_3185_){
_start:
{
uint8_t v___x_3186_; 
v___x_3186_ = lean_string_utf8_at_end(v_s_3182_, v_i_3183_);
if (v___x_3186_ == 0)
{
uint32_t v_c_3187_; uint32_t v___x_3188_; uint8_t v___x_3189_; 
v_c_3187_ = lean_string_utf8_get(v_s_3182_, v_i_3183_);
v___x_3188_ = 45;
v___x_3189_ = lean_uint32_dec_eq(v_c_3187_, v___x_3188_);
if (v___x_3189_ == 0)
{
uint32_t v___x_3190_; uint8_t v___x_3191_; 
v___x_3190_ = 43;
v___x_3191_ = lean_uint32_dec_eq(v_c_3187_, v___x_3190_);
if (v___x_3191_ == 0)
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3192_ = lean_unsigned_to_nat(0u);
v___x_3193_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3182_, v_i_3183_, v_val_3184_, v_e_3185_, v___x_3191_, v___x_3192_);
return v___x_3193_;
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3194_ = lean_string_utf8_next(v_s_3182_, v_i_3183_);
lean_dec(v_i_3183_);
v___x_3195_ = lean_unsigned_to_nat(0u);
v___x_3196_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3182_, v___x_3194_, v_val_3184_, v_e_3185_, v___x_3189_, v___x_3195_);
return v___x_3196_;
}
}
else
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3197_ = lean_string_utf8_next(v_s_3182_, v_i_3183_);
lean_dec(v_i_3183_);
v___x_3198_ = lean_unsigned_to_nat(0u);
v___x_3199_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3182_, v___x_3197_, v_val_3184_, v_e_3185_, v___x_3189_, v___x_3198_);
return v___x_3199_;
}
}
else
{
lean_object* v___x_3200_; 
lean_dec(v_val_3184_);
lean_dec(v_i_3183_);
v___x_3200_ = lean_box(0);
return v___x_3200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* v_s_3201_, lean_object* v_i_3202_, lean_object* v_val_3203_, lean_object* v_e_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3201_, v_i_3202_, v_val_3203_, v_e_3204_);
lean_dec(v_e_3204_);
lean_dec_ref(v_s_3201_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* v_s_3206_, lean_object* v_i_3207_, lean_object* v_val_3208_, lean_object* v_e_3209_){
_start:
{
uint8_t v___x_3213_; 
v___x_3213_ = lean_string_utf8_at_end(v_s_3206_, v_i_3207_);
if (v___x_3213_ == 0)
{
uint32_t v_c_3214_; uint8_t v___y_3216_; uint32_t v___x_3236_; uint8_t v___x_3237_; 
v_c_3214_ = lean_string_utf8_get(v_s_3206_, v_i_3207_);
v___x_3236_ = 48;
v___x_3237_ = lean_uint32_dec_le(v___x_3236_, v_c_3214_);
if (v___x_3237_ == 0)
{
v___y_3216_ = v___x_3213_;
goto v___jp_3215_;
}
else
{
uint32_t v___x_3238_; uint8_t v___x_3239_; 
v___x_3238_ = 57;
v___x_3239_ = lean_uint32_dec_le(v_c_3214_, v___x_3238_);
v___y_3216_ = v___x_3239_;
goto v___jp_3215_;
}
v___jp_3215_:
{
if (v___y_3216_ == 0)
{
uint32_t v___x_3217_; uint8_t v___x_3218_; 
v___x_3217_ = 95;
v___x_3218_ = lean_uint32_dec_eq(v_c_3214_, v___x_3217_);
if (v___x_3218_ == 0)
{
uint32_t v___x_3219_; uint8_t v___x_3220_; 
v___x_3219_ = 101;
v___x_3220_ = lean_uint32_dec_eq(v_c_3214_, v___x_3219_);
if (v___x_3220_ == 0)
{
uint32_t v___x_3221_; uint8_t v___x_3222_; 
v___x_3221_ = 69;
v___x_3222_ = lean_uint32_dec_eq(v_c_3214_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; 
lean_dec(v_e_3209_);
lean_dec(v_val_3208_);
lean_dec(v_i_3207_);
v___x_3223_ = lean_box(0);
return v___x_3223_;
}
else
{
goto v___jp_3210_;
}
}
else
{
goto v___jp_3210_;
}
}
else
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_string_utf8_next(v_s_3206_, v_i_3207_);
lean_dec(v_i_3207_);
v_i_3207_ = v___x_3224_;
goto _start;
}
}
else
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3226_ = lean_string_utf8_next(v_s_3206_, v_i_3207_);
lean_dec(v_i_3207_);
v___x_3227_ = lean_unsigned_to_nat(10u);
v___x_3228_ = lean_nat_mul(v___x_3227_, v_val_3208_);
lean_dec(v_val_3208_);
v___x_3229_ = lean_uint32_to_nat(v_c_3214_);
v___x_3230_ = lean_nat_add(v___x_3228_, v___x_3229_);
lean_dec(v___x_3229_);
lean_dec(v___x_3228_);
v___x_3231_ = lean_unsigned_to_nat(48u);
v___x_3232_ = lean_nat_sub(v___x_3230_, v___x_3231_);
lean_dec(v___x_3230_);
v___x_3233_ = lean_unsigned_to_nat(1u);
v___x_3234_ = lean_nat_add(v_e_3209_, v___x_3233_);
lean_dec(v_e_3209_);
v_i_3207_ = v___x_3226_;
v_val_3208_ = v___x_3232_;
v_e_3209_ = v___x_3234_;
goto _start;
}
}
}
else
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
lean_dec(v_i_3207_);
v___x_3240_ = lean_box(v___x_3213_);
v___x_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
lean_ctor_set(v___x_3241_, 1, v_e_3209_);
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v_val_3208_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3242_);
return v___x_3243_;
}
v___jp_3210_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = lean_string_utf8_next(v_s_3206_, v_i_3207_);
lean_dec(v_i_3207_);
v___x_3212_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3206_, v___x_3211_, v_val_3208_, v_e_3209_);
lean_dec(v_e_3209_);
return v___x_3212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* v_s_3244_, lean_object* v_i_3245_, lean_object* v_val_3246_, lean_object* v_e_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3244_, v_i_3245_, v_val_3246_, v_e_3247_);
lean_dec_ref(v_s_3244_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* v_s_3249_, lean_object* v_i_3250_, lean_object* v_val_3251_){
_start:
{
uint8_t v___x_3256_; 
v___x_3256_ = lean_string_utf8_at_end(v_s_3249_, v_i_3250_);
if (v___x_3256_ == 0)
{
uint32_t v_c_3257_; uint8_t v___y_3259_; uint32_t v___x_3282_; uint8_t v___x_3283_; 
v_c_3257_ = lean_string_utf8_get(v_s_3249_, v_i_3250_);
v___x_3282_ = 48;
v___x_3283_ = lean_uint32_dec_le(v___x_3282_, v_c_3257_);
if (v___x_3283_ == 0)
{
v___y_3259_ = v___x_3256_;
goto v___jp_3258_;
}
else
{
uint32_t v___x_3284_; uint8_t v___x_3285_; 
v___x_3284_ = 57;
v___x_3285_ = lean_uint32_dec_le(v_c_3257_, v___x_3284_);
v___y_3259_ = v___x_3285_;
goto v___jp_3258_;
}
v___jp_3258_:
{
if (v___y_3259_ == 0)
{
uint32_t v___x_3260_; uint8_t v___x_3261_; 
v___x_3260_ = 95;
v___x_3261_ = lean_uint32_dec_eq(v_c_3257_, v___x_3260_);
if (v___x_3261_ == 0)
{
uint32_t v___x_3262_; uint8_t v___x_3263_; 
v___x_3262_ = 46;
v___x_3263_ = lean_uint32_dec_eq(v_c_3257_, v___x_3262_);
if (v___x_3263_ == 0)
{
uint32_t v___x_3264_; uint8_t v___x_3265_; 
v___x_3264_ = 101;
v___x_3265_ = lean_uint32_dec_eq(v_c_3257_, v___x_3264_);
if (v___x_3265_ == 0)
{
uint32_t v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = 69;
v___x_3267_ = lean_uint32_dec_eq(v_c_3257_, v___x_3266_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; 
lean_dec(v_val_3251_);
lean_dec(v_i_3250_);
v___x_3268_ = lean_box(0);
return v___x_3268_;
}
else
{
goto v___jp_3252_;
}
}
else
{
goto v___jp_3252_;
}
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3269_ = lean_string_utf8_next(v_s_3249_, v_i_3250_);
lean_dec(v_i_3250_);
v___x_3270_ = lean_unsigned_to_nat(0u);
v___x_3271_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3249_, v___x_3269_, v_val_3251_, v___x_3270_);
return v___x_3271_;
}
}
else
{
lean_object* v___x_3272_; 
v___x_3272_ = lean_string_utf8_next(v_s_3249_, v_i_3250_);
lean_dec(v_i_3250_);
v_i_3250_ = v___x_3272_;
goto _start;
}
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3274_ = lean_string_utf8_next(v_s_3249_, v_i_3250_);
lean_dec(v_i_3250_);
v___x_3275_ = lean_unsigned_to_nat(10u);
v___x_3276_ = lean_nat_mul(v___x_3275_, v_val_3251_);
lean_dec(v_val_3251_);
v___x_3277_ = lean_uint32_to_nat(v_c_3257_);
v___x_3278_ = lean_nat_add(v___x_3276_, v___x_3277_);
lean_dec(v___x_3277_);
lean_dec(v___x_3276_);
v___x_3279_ = lean_unsigned_to_nat(48u);
v___x_3280_ = lean_nat_sub(v___x_3278_, v___x_3279_);
lean_dec(v___x_3278_);
v_i_3250_ = v___x_3274_;
v_val_3251_ = v___x_3280_;
goto _start;
}
}
}
else
{
lean_object* v___x_3286_; 
lean_dec(v_val_3251_);
lean_dec(v_i_3250_);
v___x_3286_ = lean_box(0);
return v___x_3286_;
}
v___jp_3252_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3253_ = lean_string_utf8_next(v_s_3249_, v_i_3250_);
lean_dec(v_i_3250_);
v___x_3254_ = lean_unsigned_to_nat(0u);
v___x_3255_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3249_, v___x_3253_, v_val_3251_, v___x_3254_);
return v___x_3255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* v_s_3287_, lean_object* v_i_3288_, lean_object* v_val_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3287_, v_i_3288_, v_val_3289_);
lean_dec_ref(v_s_3287_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* v_s_3291_){
_start:
{
lean_object* v_len_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; 
v_len_3292_ = lean_string_length(v_s_3291_);
v___x_3293_ = lean_unsigned_to_nat(0u);
v___x_3294_ = lean_nat_dec_eq(v_len_3292_, v___x_3293_);
lean_dec(v_len_3292_);
if (v___x_3294_ == 0)
{
uint32_t v_c_3295_; uint32_t v___x_3296_; uint8_t v___x_3297_; 
v_c_3295_ = lean_string_utf8_get(v_s_3291_, v___x_3293_);
v___x_3296_ = 48;
v___x_3297_ = lean_uint32_dec_le(v___x_3296_, v_c_3295_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; 
v___x_3298_ = lean_box(0);
return v___x_3298_;
}
else
{
uint32_t v___x_3299_; uint8_t v___x_3300_; 
v___x_3299_ = 57;
v___x_3300_ = lean_uint32_dec_le(v_c_3295_, v___x_3299_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; 
v___x_3301_ = lean_box(0);
return v___x_3301_;
}
else
{
lean_object* v___x_3302_; 
v___x_3302_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3291_, v___x_3293_, v___x_3293_);
return v___x_3302_;
}
}
}
else
{
lean_object* v___x_3303_; 
v___x_3303_ = lean_box(0);
return v___x_3303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* v_s_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_s_3304_);
lean_dec_ref(v_s_3304_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* v_stx_3306_){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_3308_ = l_Lean_Syntax_isLit_x3f(v___x_3307_, v_stx_3306_);
if (lean_obj_tag(v___x_3308_) == 1)
{
lean_object* v_val_3309_; lean_object* v___x_3310_; 
v_val_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_val_3309_);
lean_dec_ref_known(v___x_3308_, 1);
v___x_3310_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_val_3309_);
lean_dec(v_val_3309_);
return v___x_3310_;
}
else
{
lean_object* v___x_3311_; 
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
return v___x_3311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* v_stx_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_Syntax_isScientificLit_x3f(v_stx_3312_);
lean_dec(v_stx_3312_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* v_x_3314_){
_start:
{
switch(lean_obj_tag(v_x_3314_))
{
case 2:
{
lean_object* v_val_3315_; lean_object* v___x_3316_; 
v_val_3315_ = lean_ctor_get(v_x_3314_, 1);
lean_inc_ref(v_val_3315_);
lean_dec_ref_known(v_x_3314_, 2);
v___x_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3316_, 0, v_val_3315_);
return v___x_3316_;
}
case 3:
{
lean_object* v_rawVal_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_rawVal_3317_ = lean_ctor_get(v_x_3314_, 1);
lean_inc_ref(v_rawVal_3317_);
lean_dec_ref_known(v_x_3314_, 4);
v___x_3318_ = lean_substring_tostring(v_rawVal_3317_);
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
return v___x_3319_;
}
default: 
{
lean_object* v___x_3320_; 
lean_dec(v_x_3314_);
v___x_3320_ = lean_box(0);
return v___x_3320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* v_stx_3321_){
_start:
{
lean_object* v___x_3322_; 
v___x_3322_ = l_Lean_Syntax_isNatLit_x3f(v_stx_3321_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v___x_3323_; 
v___x_3323_ = lean_unsigned_to_nat(0u);
return v___x_3323_;
}
else
{
lean_object* v_val_3324_; 
v_val_3324_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_val_3324_);
lean_dec_ref_known(v___x_3322_, 1);
return v_val_3324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* v_stx_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Lean_Syntax_toNat(v_stx_3325_);
lean_dec(v_stx_3325_);
return v_res_3326_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = 9;
v___x_3328_ = lean_box_uint32(v___x_3327_);
return v___x_3328_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = 10;
v___x_3330_ = lean_box_uint32(v___x_3329_);
return v___x_3330_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = 13;
v___x_3332_ = lean_box_uint32(v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = 39;
v___x_3334_ = lean_box_uint32(v___x_3333_);
return v___x_3334_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = 34;
v___x_3336_ = lean_box_uint32(v___x_3335_);
return v___x_3336_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = 92;
v___x_3338_ = lean_box_uint32(v___x_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* v_s_3339_, lean_object* v_i_3340_){
_start:
{
uint32_t v_c_3341_; lean_object* v_i_3342_; uint32_t v___x_3343_; uint8_t v___x_3344_; 
v_c_3341_ = lean_string_utf8_get(v_s_3339_, v_i_3340_);
v_i_3342_ = lean_string_utf8_next(v_s_3339_, v_i_3340_);
v___x_3343_ = 92;
v___x_3344_ = lean_uint32_dec_eq(v_c_3341_, v___x_3343_);
if (v___x_3344_ == 0)
{
uint32_t v___x_3345_; uint8_t v___x_3346_; 
v___x_3345_ = 34;
v___x_3346_ = lean_uint32_dec_eq(v_c_3341_, v___x_3345_);
if (v___x_3346_ == 0)
{
uint32_t v___x_3347_; uint8_t v___x_3348_; 
v___x_3347_ = 39;
v___x_3348_ = lean_uint32_dec_eq(v_c_3341_, v___x_3347_);
if (v___x_3348_ == 0)
{
uint32_t v___x_3349_; uint8_t v___x_3350_; 
v___x_3349_ = 114;
v___x_3350_ = lean_uint32_dec_eq(v_c_3341_, v___x_3349_);
if (v___x_3350_ == 0)
{
uint32_t v___x_3351_; uint8_t v___x_3352_; 
v___x_3351_ = 110;
v___x_3352_ = lean_uint32_dec_eq(v_c_3341_, v___x_3351_);
if (v___x_3352_ == 0)
{
uint32_t v___x_3353_; uint8_t v___x_3354_; 
v___x_3353_ = 116;
v___x_3354_ = lean_uint32_dec_eq(v_c_3341_, v___x_3353_);
if (v___x_3354_ == 0)
{
uint32_t v___x_3355_; uint8_t v___x_3356_; 
v___x_3355_ = 120;
v___x_3356_ = lean_uint32_dec_eq(v_c_3341_, v___x_3355_);
if (v___x_3356_ == 0)
{
uint32_t v___x_3357_; uint8_t v___x_3358_; 
v___x_3357_ = 117;
v___x_3358_ = lean_uint32_dec_eq(v_c_3341_, v___x_3357_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; 
lean_dec(v_i_3342_);
v___x_3359_ = lean_box(0);
return v___x_3359_;
}
else
{
lean_object* v___x_3360_; 
v___x_3360_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3339_, v_i_3342_);
lean_dec(v_i_3342_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_box(0);
return v___x_3361_;
}
else
{
lean_object* v_val_3362_; lean_object* v_fst_3363_; lean_object* v_snd_3364_; lean_object* v___x_3365_; 
v_val_3362_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_val_3362_);
lean_dec_ref_known(v___x_3360_, 1);
v_fst_3363_ = lean_ctor_get(v_val_3362_, 0);
lean_inc(v_fst_3363_);
v_snd_3364_ = lean_ctor_get(v_val_3362_, 1);
lean_inc(v_snd_3364_);
lean_dec(v_val_3362_);
v___x_3365_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3339_, v_snd_3364_);
lean_dec(v_snd_3364_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v___x_3366_; 
lean_dec(v_fst_3363_);
v___x_3366_ = lean_box(0);
return v___x_3366_;
}
else
{
lean_object* v_val_3367_; lean_object* v_fst_3368_; lean_object* v_snd_3369_; lean_object* v___x_3370_; 
v_val_3367_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_val_3367_);
lean_dec_ref_known(v___x_3365_, 1);
v_fst_3368_ = lean_ctor_get(v_val_3367_, 0);
lean_inc(v_fst_3368_);
v_snd_3369_ = lean_ctor_get(v_val_3367_, 1);
lean_inc(v_snd_3369_);
lean_dec(v_val_3367_);
v___x_3370_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3339_, v_snd_3369_);
lean_dec(v_snd_3369_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v___x_3371_; 
lean_dec(v_fst_3368_);
lean_dec(v_fst_3363_);
v___x_3371_ = lean_box(0);
return v___x_3371_;
}
else
{
lean_object* v_val_3372_; lean_object* v_fst_3373_; lean_object* v_snd_3374_; lean_object* v___x_3375_; 
v_val_3372_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_val_3372_);
lean_dec_ref_known(v___x_3370_, 1);
v_fst_3373_ = lean_ctor_get(v_val_3372_, 0);
lean_inc(v_fst_3373_);
v_snd_3374_ = lean_ctor_get(v_val_3372_, 1);
lean_inc(v_snd_3374_);
lean_dec(v_val_3372_);
v___x_3375_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3339_, v_snd_3374_);
lean_dec(v_snd_3374_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v___x_3376_; 
lean_dec(v_fst_3373_);
lean_dec(v_fst_3368_);
lean_dec(v_fst_3363_);
v___x_3376_ = lean_box(0);
return v___x_3376_;
}
else
{
lean_object* v_val_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3402_; 
v_val_3377_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3379_ = v___x_3375_;
v_isShared_3380_ = v_isSharedCheck_3402_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_val_3377_);
lean_dec(v___x_3375_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3402_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v_fst_3381_; lean_object* v_snd_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3401_; 
v_fst_3381_ = lean_ctor_get(v_val_3377_, 0);
v_snd_3382_ = lean_ctor_get(v_val_3377_, 1);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_val_3377_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3384_ = v_val_3377_;
v_isShared_3385_ = v_isSharedCheck_3401_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_snd_3382_);
lean_inc(v_fst_3381_);
lean_dec(v_val_3377_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3401_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; uint32_t v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
v___x_3386_ = lean_unsigned_to_nat(16u);
v___x_3387_ = lean_nat_mul(v___x_3386_, v_fst_3363_);
lean_dec(v_fst_3363_);
v___x_3388_ = lean_nat_add(v___x_3387_, v_fst_3368_);
lean_dec(v_fst_3368_);
lean_dec(v___x_3387_);
v___x_3389_ = lean_nat_mul(v___x_3386_, v___x_3388_);
lean_dec(v___x_3388_);
v___x_3390_ = lean_nat_add(v___x_3389_, v_fst_3373_);
lean_dec(v_fst_3373_);
lean_dec(v___x_3389_);
v___x_3391_ = lean_nat_mul(v___x_3386_, v___x_3390_);
lean_dec(v___x_3390_);
v___x_3392_ = lean_nat_add(v___x_3391_, v_fst_3381_);
lean_dec(v_fst_3381_);
lean_dec(v___x_3391_);
v___x_3393_ = l_Char_ofNat(v___x_3392_);
lean_dec(v___x_3392_);
v___x_3394_ = lean_box_uint32(v___x_3393_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3394_);
v___x_3396_ = v___x_3384_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3394_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v_snd_3382_);
v___x_3396_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
lean_object* v___x_3398_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3396_);
v___x_3398_ = v___x_3379_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
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
lean_object* v___x_3403_; 
v___x_3403_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3339_, v_i_3342_);
lean_dec(v_i_3342_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v___x_3404_; 
v___x_3404_ = lean_box(0);
return v___x_3404_;
}
else
{
lean_object* v_val_3405_; lean_object* v_fst_3406_; lean_object* v_snd_3407_; lean_object* v___x_3408_; 
v_val_3405_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_val_3405_);
lean_dec_ref_known(v___x_3403_, 1);
v_fst_3406_ = lean_ctor_get(v_val_3405_, 0);
lean_inc(v_fst_3406_);
v_snd_3407_ = lean_ctor_get(v_val_3405_, 1);
lean_inc(v_snd_3407_);
lean_dec(v_val_3405_);
v___x_3408_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3339_, v_snd_3407_);
lean_dec(v_snd_3407_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v___x_3409_; 
lean_dec(v_fst_3406_);
v___x_3409_ = lean_box(0);
return v___x_3409_;
}
else
{
lean_object* v_val_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3431_; 
v_val_3410_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3412_ = v___x_3408_;
v_isShared_3413_ = v_isSharedCheck_3431_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_val_3410_);
lean_dec(v___x_3408_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3431_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v_fst_3414_; lean_object* v_snd_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3430_; 
v_fst_3414_ = lean_ctor_get(v_val_3410_, 0);
v_snd_3415_ = lean_ctor_get(v_val_3410_, 1);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_val_3410_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3417_ = v_val_3410_;
v_isShared_3418_ = v_isSharedCheck_3430_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_snd_3415_);
lean_inc(v_fst_3414_);
lean_dec(v_val_3410_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3430_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; uint32_t v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3425_; 
v___x_3419_ = lean_unsigned_to_nat(16u);
v___x_3420_ = lean_nat_mul(v___x_3419_, v_fst_3406_);
lean_dec(v_fst_3406_);
v___x_3421_ = lean_nat_add(v___x_3420_, v_fst_3414_);
lean_dec(v_fst_3414_);
lean_dec(v___x_3420_);
v___x_3422_ = l_Char_ofNat(v___x_3421_);
lean_dec(v___x_3421_);
v___x_3423_ = lean_box_uint32(v___x_3422_);
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v___x_3423_);
v___x_3425_ = v___x_3417_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3423_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v_snd_3415_);
v___x_3425_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3427_; 
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v___x_3425_);
v___x_3427_ = v___x_3412_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
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
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
v___x_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3432_);
lean_ctor_set(v___x_3433_, 1, v_i_3342_);
v___x_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
return v___x_3434_;
}
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3435_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
v___x_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
lean_ctor_set(v___x_3436_, 1, v_i_3342_);
v___x_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
return v___x_3437_;
}
}
else
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3438_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
v___x_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
lean_ctor_set(v___x_3439_, 1, v_i_3342_);
v___x_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
return v___x_3440_;
}
}
else
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3441_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
v___x_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
lean_ctor_set(v___x_3442_, 1, v_i_3342_);
v___x_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
return v___x_3443_;
}
}
else
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
v___x_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
lean_ctor_set(v___x_3445_, 1, v_i_3342_);
v___x_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
return v___x_3446_;
}
}
else
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3447_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
v___x_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
lean_ctor_set(v___x_3448_, 1, v_i_3342_);
v___x_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3448_);
return v___x_3449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* v_s_3450_, lean_object* v_i_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_Syntax_decodeQuotedChar(v_s_3450_, v_i_3451_);
lean_dec(v_i_3451_);
lean_dec_ref(v_s_3450_);
return v_res_3452_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t v___y_3453_){
_start:
{
uint32_t v___x_3454_; uint8_t v___x_3455_; 
v___x_3454_ = 32;
v___x_3455_ = lean_uint32_dec_eq(v___y_3453_, v___x_3454_);
if (v___x_3455_ == 0)
{
uint32_t v___x_3456_; uint8_t v___x_3457_; 
v___x_3456_ = 9;
v___x_3457_ = lean_uint32_dec_eq(v___y_3453_, v___x_3456_);
if (v___x_3457_ == 0)
{
uint32_t v___x_3458_; uint8_t v___x_3459_; 
v___x_3458_ = 13;
v___x_3459_ = lean_uint32_dec_eq(v___y_3453_, v___x_3458_);
if (v___x_3459_ == 0)
{
uint32_t v___x_3460_; uint8_t v___x_3461_; 
v___x_3460_ = 10;
v___x_3461_ = lean_uint32_dec_eq(v___y_3453_, v___x_3460_);
return v___x_3461_;
}
else
{
return v___x_3459_;
}
}
else
{
return v___x_3457_;
}
}
else
{
return v___x_3455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* v___y_3462_){
_start:
{
uint32_t v___y_264__boxed_3463_; uint8_t v_res_3464_; lean_object* v_r_3465_; 
v___y_264__boxed_3463_ = lean_unbox_uint32(v___y_3462_);
lean_dec(v___y_3462_);
v_res_3464_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_264__boxed_3463_);
v_r_3465_ = lean_box(v_res_3464_);
return v_r_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* v_s_3467_, lean_object* v_i_3468_){
_start:
{
lean_object* v___f_3469_; uint32_t v___x_3474_; uint32_t v___x_3475_; uint8_t v___x_3476_; 
v___f_3469_ = ((lean_object*)(l_Lean_Syntax_decodeStringGap___closed__0));
v___x_3474_ = lean_string_utf8_get(v_s_3467_, v_i_3468_);
v___x_3475_ = 32;
v___x_3476_ = lean_uint32_dec_eq(v___x_3474_, v___x_3475_);
if (v___x_3476_ == 0)
{
uint32_t v___x_3477_; uint8_t v___x_3478_; 
v___x_3477_ = 9;
v___x_3478_ = lean_uint32_dec_eq(v___x_3474_, v___x_3477_);
if (v___x_3478_ == 0)
{
uint32_t v___x_3479_; uint8_t v___x_3480_; 
v___x_3479_ = 13;
v___x_3480_ = lean_uint32_dec_eq(v___x_3474_, v___x_3479_);
if (v___x_3480_ == 0)
{
uint32_t v___x_3481_; uint8_t v___x_3482_; 
v___x_3481_ = 10;
v___x_3482_ = lean_uint32_dec_eq(v___x_3474_, v___x_3481_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; 
lean_dec_ref(v_s_3467_);
v___x_3483_ = lean_box(0);
return v___x_3483_;
}
else
{
goto v___jp_3470_;
}
}
else
{
goto v___jp_3470_;
}
}
else
{
goto v___jp_3470_;
}
}
else
{
goto v___jp_3470_;
}
v___jp_3470_:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = lean_string_utf8_next(v_s_3467_, v_i_3468_);
v___x_3472_ = lean_string_nextwhile(v_s_3467_, v___f_3469_, v___x_3471_);
v___x_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
return v___x_3473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* v_s_3484_, lean_object* v_i_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Lean_Syntax_decodeStringGap(v_s_3484_, v_i_3485_);
lean_dec(v_i_3485_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* v_s_3487_, lean_object* v_i_3488_, lean_object* v_acc_3489_){
_start:
{
uint32_t v_c_3490_; uint32_t v___x_3491_; uint8_t v___x_3492_; 
v_c_3490_ = lean_string_utf8_get(v_s_3487_, v_i_3488_);
v___x_3491_ = 34;
v___x_3492_ = lean_uint32_dec_eq(v_c_3490_, v___x_3491_);
if (v___x_3492_ == 0)
{
lean_object* v_i_3493_; uint8_t v___x_3494_; 
v_i_3493_ = lean_string_utf8_next(v_s_3487_, v_i_3488_);
lean_dec(v_i_3488_);
v___x_3494_ = lean_string_utf8_at_end(v_s_3487_, v_i_3493_);
if (v___x_3494_ == 0)
{
uint32_t v___x_3495_; uint8_t v___x_3496_; 
v___x_3495_ = 92;
v___x_3496_ = lean_uint32_dec_eq(v_c_3490_, v___x_3495_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
v___x_3497_ = lean_string_push(v_acc_3489_, v_c_3490_);
v_i_3488_ = v_i_3493_;
v_acc_3489_ = v___x_3497_;
goto _start;
}
else
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_Syntax_decodeQuotedChar(v_s_3487_, v_i_3493_);
if (lean_obj_tag(v___x_3499_) == 1)
{
lean_object* v_val_3500_; lean_object* v_fst_3501_; lean_object* v_snd_3502_; uint32_t v___x_3503_; lean_object* v___x_3504_; 
lean_dec(v_i_3493_);
v_val_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_val_3500_);
lean_dec_ref_known(v___x_3499_, 1);
v_fst_3501_ = lean_ctor_get(v_val_3500_, 0);
lean_inc(v_fst_3501_);
v_snd_3502_ = lean_ctor_get(v_val_3500_, 1);
lean_inc(v_snd_3502_);
lean_dec(v_val_3500_);
v___x_3503_ = lean_unbox_uint32(v_fst_3501_);
lean_dec(v_fst_3501_);
v___x_3504_ = lean_string_push(v_acc_3489_, v___x_3503_);
v_i_3488_ = v_snd_3502_;
v_acc_3489_ = v___x_3504_;
goto _start;
}
else
{
lean_object* v___x_3506_; 
lean_dec(v___x_3499_);
lean_inc_ref(v_s_3487_);
v___x_3506_ = l_Lean_Syntax_decodeStringGap(v_s_3487_, v_i_3493_);
lean_dec(v_i_3493_);
if (lean_obj_tag(v___x_3506_) == 1)
{
lean_object* v_val_3507_; 
v_val_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_val_3507_);
lean_dec_ref_known(v___x_3506_, 1);
v_i_3488_ = v_val_3507_;
goto _start;
}
else
{
lean_object* v___x_3509_; 
lean_dec(v___x_3506_);
lean_dec_ref(v_acc_3489_);
lean_dec_ref(v_s_3487_);
v___x_3509_ = lean_box(0);
return v___x_3509_;
}
}
}
}
else
{
lean_object* v___x_3510_; 
lean_dec(v_i_3493_);
lean_dec_ref(v_acc_3489_);
lean_dec_ref(v_s_3487_);
v___x_3510_ = lean_box(0);
return v___x_3510_;
}
}
else
{
lean_object* v___x_3511_; 
lean_dec(v_i_3488_);
lean_dec_ref(v_s_3487_);
v___x_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3511_, 0, v_acc_3489_);
return v___x_3511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* v_s_3512_, lean_object* v_i_3513_, lean_object* v_num_3514_){
_start:
{
uint32_t v_c_3515_; lean_object* v_i_3516_; uint32_t v___x_3517_; uint8_t v___x_3518_; 
v_c_3515_ = lean_string_utf8_get(v_s_3512_, v_i_3513_);
v_i_3516_ = lean_string_utf8_next(v_s_3512_, v_i_3513_);
lean_dec(v_i_3513_);
v___x_3517_ = 35;
v___x_3518_ = lean_uint32_dec_eq(v_c_3515_, v___x_3517_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3519_ = lean_string_utf8_byte_size(v_s_3512_);
v___x_3520_ = lean_unsigned_to_nat(1u);
v___x_3521_ = lean_nat_add(v_num_3514_, v___x_3520_);
lean_dec(v_num_3514_);
v___x_3522_ = lean_nat_sub(v___x_3519_, v___x_3521_);
lean_dec(v___x_3521_);
v___x_3523_ = lean_string_utf8_extract(v_s_3512_, v_i_3516_, v___x_3522_);
lean_dec(v___x_3522_);
lean_dec(v_i_3516_);
return v___x_3523_;
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3524_ = lean_unsigned_to_nat(1u);
v___x_3525_ = lean_nat_add(v_num_3514_, v___x_3524_);
lean_dec(v_num_3514_);
v_i_3513_ = v_i_3516_;
v_num_3514_ = v___x_3525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* v_s_3527_, lean_object* v_i_3528_, lean_object* v_num_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3527_, v_i_3528_, v_num_3529_);
lean_dec_ref(v_s_3527_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* v_s_3531_){
_start:
{
lean_object* v___x_3532_; uint32_t v___x_3533_; uint32_t v___x_3534_; uint8_t v___x_3535_; 
v___x_3532_ = lean_unsigned_to_nat(0u);
v___x_3533_ = lean_string_utf8_get(v_s_3531_, v___x_3532_);
v___x_3534_ = 114;
v___x_3535_ = lean_uint32_dec_eq(v___x_3533_, v___x_3534_);
if (v___x_3535_ == 0)
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3536_ = lean_unsigned_to_nat(1u);
v___x_3537_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_3538_ = l_Lean_Syntax_decodeStrLitAux(v_s_3531_, v___x_3536_, v___x_3537_);
return v___x_3538_;
}
else
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = lean_unsigned_to_nat(1u);
v___x_3540_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3531_, v___x_3539_, v___x_3532_);
lean_dec_ref(v_s_3531_);
v___x_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
return v___x_3541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* v_stx_3542_){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_3544_ = l_Lean_Syntax_isLit_x3f(v___x_3543_, v_stx_3542_);
if (lean_obj_tag(v___x_3544_) == 1)
{
lean_object* v_val_3545_; lean_object* v___x_3546_; 
v_val_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_val_3545_);
lean_dec_ref_known(v___x_3544_, 1);
v___x_3546_ = l_Lean_Syntax_decodeStrLit(v_val_3545_);
return v___x_3546_;
}
else
{
lean_object* v___x_3547_; 
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
return v___x_3547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* v_stx_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_Lean_Syntax_isStrLit_x3f(v_stx_3548_);
lean_dec(v_stx_3548_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* v_s_3550_){
_start:
{
lean_object* v___x_3551_; uint32_t v_c_3552_; uint32_t v___x_3553_; uint8_t v___x_3554_; 
v___x_3551_ = lean_unsigned_to_nat(1u);
v_c_3552_ = lean_string_utf8_get(v_s_3550_, v___x_3551_);
v___x_3553_ = 92;
v___x_3554_ = lean_uint32_dec_eq(v_c_3552_, v___x_3553_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = lean_box_uint32(v_c_3552_);
v___x_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3555_);
return v___x_3556_;
}
else
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = lean_unsigned_to_nat(2u);
v___x_3558_ = l_Lean_Syntax_decodeQuotedChar(v_s_3550_, v___x_3557_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v___x_3559_; 
v___x_3559_ = lean_box(0);
return v___x_3559_;
}
else
{
lean_object* v_val_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3568_; 
v_val_3560_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3562_ = v___x_3558_;
v_isShared_3563_ = v_isSharedCheck_3568_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_val_3560_);
lean_dec(v___x_3558_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3568_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v_fst_3564_; lean_object* v___x_3566_; 
v_fst_3564_ = lean_ctor_get(v_val_3560_, 0);
lean_inc(v_fst_3564_);
lean_dec(v_val_3560_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 0, v_fst_3564_);
v___x_3566_ = v___x_3562_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_fst_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* v_s_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_Lean_Syntax_decodeCharLit(v_s_3569_);
lean_dec_ref(v_s_3569_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* v_stx_3571_){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_3573_ = l_Lean_Syntax_isLit_x3f(v___x_3572_, v_stx_3571_);
if (lean_obj_tag(v___x_3573_) == 1)
{
lean_object* v_val_3574_; lean_object* v___x_3575_; 
v_val_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_val_3574_);
lean_dec_ref_known(v___x_3573_, 1);
v___x_3575_ = l_Lean_Syntax_decodeCharLit(v_val_3574_);
lean_dec(v_val_3574_);
return v___x_3575_;
}
else
{
lean_object* v___x_3576_; 
lean_dec(v___x_3573_);
v___x_3576_ = lean_box(0);
return v___x_3576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* v_stx_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Lean_Syntax_isCharLit_x3f(v_stx_3577_);
lean_dec(v_stx_3577_);
return v_res_3578_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t v___y_3579_){
_start:
{
uint8_t v___y_3597_; uint32_t v___x_3602_; uint8_t v___x_3603_; 
v___x_3602_ = 65;
v___x_3603_ = lean_uint32_dec_le(v___x_3602_, v___y_3579_);
if (v___x_3603_ == 0)
{
v___y_3597_ = v___x_3603_;
goto v___jp_3596_;
}
else
{
uint32_t v___x_3604_; uint8_t v___x_3605_; 
v___x_3604_ = 90;
v___x_3605_ = lean_uint32_dec_le(v___y_3579_, v___x_3604_);
v___y_3597_ = v___x_3605_;
goto v___jp_3596_;
}
v___jp_3580_:
{
uint32_t v___x_3581_; uint8_t v___x_3582_; 
v___x_3581_ = 95;
v___x_3582_ = lean_uint32_dec_eq(v___y_3579_, v___x_3581_);
if (v___x_3582_ == 0)
{
uint32_t v___x_3583_; uint8_t v___x_3584_; 
v___x_3583_ = 39;
v___x_3584_ = lean_uint32_dec_eq(v___y_3579_, v___x_3583_);
if (v___x_3584_ == 0)
{
uint32_t v___x_3585_; uint8_t v___x_3586_; 
v___x_3585_ = 33;
v___x_3586_ = lean_uint32_dec_eq(v___y_3579_, v___x_3585_);
if (v___x_3586_ == 0)
{
uint32_t v___x_3587_; uint8_t v___x_3588_; 
v___x_3587_ = 63;
v___x_3588_ = lean_uint32_dec_eq(v___y_3579_, v___x_3587_);
if (v___x_3588_ == 0)
{
uint8_t v___x_3589_; 
v___x_3589_ = l_Lean_isLetterLike(v___y_3579_);
if (v___x_3589_ == 0)
{
uint8_t v___x_3590_; 
v___x_3590_ = l_Lean_isSubScriptAlnum(v___y_3579_);
return v___x_3590_;
}
else
{
return v___x_3589_;
}
}
else
{
return v___x_3588_;
}
}
else
{
return v___x_3586_;
}
}
else
{
return v___x_3584_;
}
}
else
{
return v___x_3582_;
}
}
v___jp_3591_:
{
uint32_t v___x_3592_; uint8_t v___x_3593_; 
v___x_3592_ = 48;
v___x_3593_ = lean_uint32_dec_le(v___x_3592_, v___y_3579_);
if (v___x_3593_ == 0)
{
goto v___jp_3580_;
}
else
{
uint32_t v___x_3594_; uint8_t v___x_3595_; 
v___x_3594_ = 57;
v___x_3595_ = lean_uint32_dec_le(v___y_3579_, v___x_3594_);
if (v___x_3595_ == 0)
{
goto v___jp_3580_;
}
else
{
return v___x_3595_;
}
}
}
v___jp_3596_:
{
if (v___y_3597_ == 0)
{
uint32_t v___x_3598_; uint8_t v___x_3599_; 
v___x_3598_ = 97;
v___x_3599_ = lean_uint32_dec_le(v___x_3598_, v___y_3579_);
if (v___x_3599_ == 0)
{
goto v___jp_3591_;
}
else
{
uint32_t v___x_3600_; uint8_t v___x_3601_; 
v___x_3600_ = 122;
v___x_3601_ = lean_uint32_dec_le(v___y_3579_, v___x_3600_);
if (v___x_3601_ == 0)
{
goto v___jp_3591_;
}
else
{
return v___x_3601_;
}
}
}
else
{
return v___y_3597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* v___y_3606_){
_start:
{
uint32_t v___y_509__boxed_3607_; uint8_t v_res_3608_; lean_object* v_r_3609_; 
v___y_509__boxed_3607_ = lean_unbox_uint32(v___y_3606_);
lean_dec(v___y_3606_);
v_res_3608_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_509__boxed_3607_);
v_r_3609_ = lean_box(v_res_3608_);
return v_r_3609_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t v___x_3610_, uint32_t v___x_3611_, uint32_t v___y_3612_){
_start:
{
uint8_t v___x_3613_; 
v___x_3613_ = lean_uint32_dec_le(v___x_3610_, v___y_3612_);
if (v___x_3613_ == 0)
{
return v___x_3613_;
}
else
{
uint8_t v___x_3614_; 
v___x_3614_ = lean_uint32_dec_le(v___y_3612_, v___x_3611_);
return v___x_3614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* v___x_3615_, lean_object* v___x_3616_, lean_object* v___y_3617_){
_start:
{
uint32_t v___x_564__boxed_3618_; uint32_t v___x_565__boxed_3619_; uint32_t v___y_566__boxed_3620_; uint8_t v_res_3621_; lean_object* v_r_3622_; 
v___x_564__boxed_3618_ = lean_unbox_uint32(v___x_3615_);
lean_dec(v___x_3615_);
v___x_565__boxed_3619_ = lean_unbox_uint32(v___x_3616_);
lean_dec(v___x_3616_);
v___y_566__boxed_3620_ = lean_unbox_uint32(v___y_3617_);
lean_dec(v___y_3617_);
v_res_3621_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___x_564__boxed_3618_, v___x_565__boxed_3619_, v___y_566__boxed_3620_);
v_r_3622_ = lean_box(v_res_3621_);
return v_r_3622_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t v___x_3623_, uint8_t v___x_3624_, uint32_t v_x_3625_){
_start:
{
uint32_t v___x_3626_; uint8_t v___x_3627_; 
v___x_3626_ = 187;
v___x_3627_ = lean_uint32_dec_eq(v_x_3625_, v___x_3626_);
if (v___x_3627_ == 0)
{
return v___x_3623_;
}
else
{
return v___x_3624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* v___x_3628_, lean_object* v___x_3629_, lean_object* v_x_3630_){
_start:
{
uint8_t v___x_577__boxed_3631_; uint8_t v___x_578__boxed_3632_; uint32_t v_x_579__boxed_3633_; uint8_t v_res_3634_; lean_object* v_r_3635_; 
v___x_577__boxed_3631_ = lean_unbox(v___x_3628_);
v___x_578__boxed_3632_ = lean_unbox(v___x_3629_);
v_x_579__boxed_3633_ = lean_unbox_uint32(v_x_3630_);
lean_dec(v_x_3630_);
v_res_3634_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v___x_577__boxed_3631_, v___x_578__boxed_3632_, v_x_579__boxed_3633_);
v_r_3635_ = lean_box(v_res_3634_);
return v_r_3635_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = 48;
v___x_3638_ = lean_box_uint32(v___x_3637_);
return v___x_3638_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2(void){
_start:
{
uint32_t v___x_3639_; lean_object* v___x_3640_; 
v___x_3639_ = 57;
v___x_3640_ = lean_box_uint32(v___x_3639_);
return v___x_3640_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1(void){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___f_3643_; 
v___x_3641_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1;
v___x_3642_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2;
v___f_3643_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3643_, 0, v___x_3641_);
lean_closure_set(v___f_3643_, 1, v___x_3642_);
return v___f_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* v_ss_3644_, lean_object* v_acc_3645_){
_start:
{
lean_object* v_ss_3647_; lean_object* v_acc_3648_; uint8_t v___x_3657_; 
lean_inc_ref(v_ss_3644_);
v___x_3657_ = lean_substring_isempty(v_ss_3644_);
if (v___x_3657_ == 0)
{
uint32_t v_curr_3658_; uint32_t v___x_3659_; uint8_t v___x_3660_; 
lean_inc_ref(v_ss_3644_);
v_curr_3658_ = lean_substring_front(v_ss_3644_);
v___x_3659_ = 171;
v___x_3660_ = lean_uint32_dec_eq(v_curr_3658_, v___x_3659_);
if (v___x_3660_ == 0)
{
lean_object* v___f_3661_; uint8_t v___y_3693_; uint32_t v___x_3698_; uint8_t v___x_3699_; 
v___f_3661_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0));
v___x_3698_ = 65;
v___x_3699_ = lean_uint32_dec_le(v___x_3698_, v_curr_3658_);
if (v___x_3699_ == 0)
{
v___y_3693_ = v___x_3699_;
goto v___jp_3692_;
}
else
{
uint32_t v___x_3700_; uint8_t v___x_3701_; 
v___x_3700_ = 90;
v___x_3701_ = lean_uint32_dec_le(v_curr_3658_, v___x_3700_);
v___y_3693_ = v___x_3701_;
goto v___jp_3692_;
}
v___jp_3662_:
{
lean_object* v_idPart_3663_; lean_object* v_startPos_3664_; lean_object* v_stopPos_3665_; lean_object* v_startPos_3666_; lean_object* v_stopPos_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
lean_inc_ref(v_ss_3644_);
v_idPart_3663_ = lean_substring_takewhile(v_ss_3644_, v___f_3661_);
v_startPos_3664_ = lean_ctor_get(v_idPart_3663_, 1);
lean_inc(v_startPos_3664_);
v_stopPos_3665_ = lean_ctor_get(v_idPart_3663_, 2);
lean_inc(v_stopPos_3665_);
v_startPos_3666_ = lean_ctor_get(v_ss_3644_, 1);
v_stopPos_3667_ = lean_ctor_get(v_ss_3644_, 2);
v___x_3668_ = lean_nat_sub(v_stopPos_3665_, v_startPos_3664_);
lean_dec(v_startPos_3664_);
lean_dec(v_stopPos_3665_);
v___x_3669_ = lean_nat_sub(v_stopPos_3667_, v_startPos_3666_);
v___x_3670_ = lean_substring_extract(v_ss_3644_, v___x_3668_, v___x_3669_);
v___x_3671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3671_, 0, v_idPart_3663_);
lean_ctor_set(v___x_3671_, 1, v_acc_3645_);
v_ss_3647_ = v___x_3670_;
v_acc_3648_ = v___x_3671_;
goto v___jp_3646_;
}
v___jp_3672_:
{
uint32_t v___x_3673_; uint8_t v___x_3674_; 
v___x_3673_ = 95;
v___x_3674_ = lean_uint32_dec_eq(v_curr_3658_, v___x_3673_);
if (v___x_3674_ == 0)
{
uint8_t v___x_3675_; 
v___x_3675_ = l_Lean_isLetterLike(v_curr_3658_);
if (v___x_3675_ == 0)
{
uint32_t v___x_3676_; uint8_t v___x_3677_; 
v___x_3676_ = 48;
v___x_3677_ = lean_uint32_dec_le(v___x_3676_, v_curr_3658_);
if (v___x_3677_ == 0)
{
lean_object* v___x_3678_; 
lean_dec(v_acc_3645_);
lean_dec_ref(v_ss_3644_);
v___x_3678_ = lean_box(0);
return v___x_3678_;
}
else
{
uint32_t v___x_3679_; uint8_t v___x_3680_; 
v___x_3679_ = 57;
v___x_3680_ = lean_uint32_dec_le(v_curr_3658_, v___x_3679_);
if (v___x_3680_ == 0)
{
lean_object* v___x_3681_; 
lean_dec(v_acc_3645_);
lean_dec_ref(v_ss_3644_);
v___x_3681_ = lean_box(0);
return v___x_3681_;
}
else
{
lean_object* v___f_3682_; lean_object* v_idPart_3683_; lean_object* v_startPos_3684_; lean_object* v_stopPos_3685_; lean_object* v_startPos_3686_; lean_object* v_stopPos_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___f_3682_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1, &l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1);
lean_inc_ref(v_ss_3644_);
v_idPart_3683_ = lean_substring_takewhile(v_ss_3644_, v___f_3682_);
v_startPos_3684_ = lean_ctor_get(v_idPart_3683_, 1);
lean_inc(v_startPos_3684_);
v_stopPos_3685_ = lean_ctor_get(v_idPart_3683_, 2);
lean_inc(v_stopPos_3685_);
v_startPos_3686_ = lean_ctor_get(v_ss_3644_, 1);
v_stopPos_3687_ = lean_ctor_get(v_ss_3644_, 2);
v___x_3688_ = lean_nat_sub(v_stopPos_3685_, v_startPos_3684_);
lean_dec(v_startPos_3684_);
lean_dec(v_stopPos_3685_);
v___x_3689_ = lean_nat_sub(v_stopPos_3687_, v_startPos_3686_);
v___x_3690_ = lean_substring_extract(v_ss_3644_, v___x_3688_, v___x_3689_);
v___x_3691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3691_, 0, v_idPart_3683_);
lean_ctor_set(v___x_3691_, 1, v_acc_3645_);
v_ss_3647_ = v___x_3690_;
v_acc_3648_ = v___x_3691_;
goto v___jp_3646_;
}
}
}
else
{
goto v___jp_3662_;
}
}
else
{
goto v___jp_3662_;
}
}
v___jp_3692_:
{
if (v___y_3693_ == 0)
{
uint32_t v___x_3694_; uint8_t v___x_3695_; 
v___x_3694_ = 97;
v___x_3695_ = lean_uint32_dec_le(v___x_3694_, v_curr_3658_);
if (v___x_3695_ == 0)
{
goto v___jp_3672_;
}
else
{
uint32_t v___x_3696_; uint8_t v___x_3697_; 
v___x_3696_ = 122;
v___x_3697_ = lean_uint32_dec_le(v_curr_3658_, v___x_3696_);
if (v___x_3697_ == 0)
{
goto v___jp_3672_;
}
else
{
goto v___jp_3662_;
}
}
}
else
{
goto v___jp_3662_;
}
}
}
else
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___f_3704_; lean_object* v_escapedPart_3705_; lean_object* v_str_3706_; lean_object* v_startPos_3707_; lean_object* v_stopPos_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3729_; 
v___x_3702_ = lean_box(v___x_3660_);
v___x_3703_ = lean_box(v___x_3657_);
v___f_3704_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3704_, 0, v___x_3702_);
lean_closure_set(v___f_3704_, 1, v___x_3703_);
lean_inc_ref(v_ss_3644_);
v_escapedPart_3705_ = lean_substring_takewhile(v_ss_3644_, v___f_3704_);
v_str_3706_ = lean_ctor_get(v_escapedPart_3705_, 0);
v_startPos_3707_ = lean_ctor_get(v_escapedPart_3705_, 1);
v_stopPos_3708_ = lean_ctor_get(v_escapedPart_3705_, 2);
v_isSharedCheck_3729_ = !lean_is_exclusive(v_escapedPart_3705_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3710_ = v_escapedPart_3705_;
v_isShared_3711_ = v_isSharedCheck_3729_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_stopPos_3708_);
lean_inc(v_startPos_3707_);
lean_inc(v_str_3706_);
lean_dec(v_escapedPart_3705_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3729_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v_startPos_3712_; lean_object* v_stopPos_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v_escapedPart_3717_; 
v_startPos_3712_ = lean_ctor_get(v_ss_3644_, 1);
v_stopPos_3713_ = lean_ctor_get(v_ss_3644_, 2);
v___x_3714_ = lean_string_utf8_next(v_str_3706_, v_stopPos_3708_);
lean_dec(v_stopPos_3708_);
lean_inc(v_stopPos_3713_);
v___x_3715_ = lean_string_pos_min(v_stopPos_3713_, v___x_3714_);
lean_inc(v___x_3715_);
lean_inc(v_startPos_3707_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 2, v___x_3715_);
v_escapedPart_3717_ = v___x_3710_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_str_3706_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_startPos_3707_);
lean_ctor_set(v_reuseFailAlloc_3728_, 2, v___x_3715_);
v_escapedPart_3717_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; uint32_t v___x_3720_; uint32_t v___x_3721_; uint8_t v___x_3722_; 
v___x_3718_ = lean_nat_sub(v___x_3715_, v_startPos_3707_);
lean_dec(v_startPos_3707_);
lean_dec(v___x_3715_);
lean_inc(v___x_3718_);
lean_inc_ref_n(v_escapedPart_3717_, 2);
v___x_3719_ = lean_substring_prev(v_escapedPart_3717_, v___x_3718_);
v___x_3720_ = lean_substring_get(v_escapedPart_3717_, v___x_3719_);
v___x_3721_ = 187;
v___x_3722_ = lean_uint32_dec_eq(v___x_3720_, v___x_3721_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; 
lean_dec(v___x_3718_);
lean_dec_ref(v_escapedPart_3717_);
lean_dec(v_acc_3645_);
lean_dec_ref(v_ss_3644_);
v___x_3723_ = lean_box(0);
return v___x_3723_;
}
else
{
if (v___x_3657_ == 0)
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3724_ = lean_nat_sub(v_stopPos_3713_, v_startPos_3712_);
v___x_3725_ = lean_substring_extract(v_ss_3644_, v___x_3718_, v___x_3724_);
v___x_3726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3726_, 0, v_escapedPart_3717_);
lean_ctor_set(v___x_3726_, 1, v_acc_3645_);
v_ss_3647_ = v___x_3725_;
v_acc_3648_ = v___x_3726_;
goto v___jp_3646_;
}
else
{
lean_object* v___x_3727_; 
lean_dec(v___x_3718_);
lean_dec_ref(v_escapedPart_3717_);
lean_dec(v_acc_3645_);
lean_dec_ref(v_ss_3644_);
v___x_3727_ = lean_box(0);
return v___x_3727_;
}
}
}
}
}
}
else
{
lean_object* v___x_3730_; 
lean_dec(v_acc_3645_);
lean_dec_ref(v_ss_3644_);
v___x_3730_ = lean_box(0);
return v___x_3730_;
}
v___jp_3646_:
{
uint32_t v___x_3649_; uint32_t v___x_3650_; uint8_t v___x_3651_; 
lean_inc_ref(v_ss_3647_);
v___x_3649_ = lean_substring_front(v_ss_3647_);
v___x_3650_ = 46;
v___x_3651_ = lean_uint32_dec_eq(v___x_3649_, v___x_3650_);
if (v___x_3651_ == 0)
{
uint8_t v___x_3652_; 
v___x_3652_ = lean_substring_isempty(v_ss_3647_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; 
lean_dec(v_acc_3648_);
v___x_3653_ = lean_box(0);
return v___x_3653_;
}
else
{
return v_acc_3648_;
}
}
else
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = lean_unsigned_to_nat(1u);
v___x_3655_ = lean_substring_drop(v_ss_3647_, v___x_3654_);
v_ss_3644_ = v___x_3655_;
v_acc_3645_ = v_acc_3648_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* v_ss_3731_){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3732_ = lean_box(0);
v___x_3733_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_ss_3731_, v___x_3732_);
v___x_3734_ = l_List_reverse___redArg(v___x_3733_);
return v___x_3734_;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3738_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3739_ = lean_unsigned_to_nat(10u);
v___x_3740_ = lean_unsigned_to_nat(1254u);
v___x_3741_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3742_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3743_ = l_mkPanicMessageWithDecl(v___x_3742_, v___x_3741_, v___x_3740_, v___x_3739_, v___x_3738_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object* v_init_3744_, lean_object* v_x_3745_){
_start:
{
if (lean_obj_tag(v_x_3745_) == 0)
{
lean_inc(v_init_3744_);
return v_init_3744_;
}
else
{
lean_object* v_head_3746_; lean_object* v_tail_3747_; lean_object* v___x_3748_; lean_object* v_comp_3749_; uint32_t v___x_3750_; uint32_t v___x_3751_; uint8_t v___x_3752_; 
v_head_3746_ = lean_ctor_get(v_x_3745_, 0);
lean_inc(v_head_3746_);
v_tail_3747_ = lean_ctor_get(v_x_3745_, 1);
lean_inc(v_tail_3747_);
lean_dec_ref_known(v_x_3745_, 2);
v___x_3748_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3744_, v_tail_3747_);
v_comp_3749_ = lean_substring_tostring(v_head_3746_);
lean_inc_ref(v_comp_3749_);
v___x_3750_ = lean_string_front(v_comp_3749_);
v___x_3751_ = 171;
v___x_3752_ = lean_uint32_dec_eq(v___x_3750_, v___x_3751_);
if (v___x_3752_ == 0)
{
uint32_t v___x_3753_; uint8_t v___x_3754_; 
v___x_3753_ = 48;
v___x_3754_ = lean_uint32_dec_le(v___x_3753_, v___x_3750_);
if (v___x_3754_ == 0)
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_Name_str___override(v___x_3748_, v_comp_3749_);
return v___x_3755_;
}
else
{
uint32_t v___x_3756_; uint8_t v___x_3757_; 
v___x_3756_ = 57;
v___x_3757_ = lean_uint32_dec_le(v___x_3750_, v___x_3756_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Lean_Name_str___override(v___x_3748_, v_comp_3749_);
return v___x_3758_;
}
else
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3749_);
lean_dec_ref(v_comp_3749_);
if (lean_obj_tag(v___x_3759_) == 1)
{
lean_object* v_val_3760_; lean_object* v___x_3761_; 
v_val_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_val_3760_);
lean_dec_ref_known(v___x_3759_, 1);
v___x_3761_ = l_Lean_Name_num___override(v___x_3748_, v_val_3760_);
return v___x_3761_;
}
else
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
lean_dec(v___x_3759_);
lean_dec(v___x_3748_);
v___x_3762_ = lean_obj_once(&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3, &l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3763_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3762_);
return v___x_3763_;
}
}
}
}
else
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3764_ = lean_unsigned_to_nat(1u);
v___x_3765_ = lean_string_drop(v_comp_3749_, v___x_3764_);
v___x_3766_ = lean_string_dropright(v___x_3765_, v___x_3764_);
v___x_3767_ = l_Lean_Name_str___override(v___x_3748_, v___x_3766_);
return v___x_3767_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_init_3768_, lean_object* v_x_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3768_, v_x_3769_);
lean_dec(v_init_3768_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3771_){
_start:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = lean_box(0);
v___x_3773_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3771_, v___x_3772_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v___x_3774_; 
v___x_3774_ = lean_box(0);
return v___x_3774_;
}
else
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3775_ = lean_box(0);
v___x_3776_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v___x_3775_, v___x_3773_);
return v___x_3776_;
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3777_){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3778_ = lean_unsigned_to_nat(0u);
v___x_3779_ = lean_string_utf8_byte_size(v_s_3777_);
v___x_3780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3780_, 0, v_s_3777_);
lean_ctor_set(v___x_3780_, 1, v___x_3778_);
lean_ctor_set(v___x_3780_, 2, v___x_3779_);
v___x_3781_ = l_Substring_Raw_toName(v___x_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3782_){
_start:
{
lean_object* v___x_3783_; uint32_t v___x_3784_; uint32_t v___x_3785_; uint8_t v___x_3786_; 
v___x_3783_ = lean_unsigned_to_nat(0u);
v___x_3784_ = lean_string_utf8_get(v_s_3782_, v___x_3783_);
v___x_3785_ = 96;
v___x_3786_ = lean_uint32_dec_eq(v___x_3784_, v___x_3785_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3787_; 
lean_dec_ref(v_s_3782_);
v___x_3787_ = lean_box(0);
return v___x_3787_;
}
else
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3788_ = lean_string_utf8_byte_size(v_s_3782_);
v___x_3789_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3789_, 0, v_s_3782_);
lean_ctor_set(v___x_3789_, 1, v___x_3783_);
lean_ctor_set(v___x_3789_, 2, v___x_3788_);
v___x_3790_ = lean_unsigned_to_nat(1u);
v___x_3791_ = lean_substring_drop(v___x_3789_, v___x_3790_);
v___x_3792_ = l_Substring_Raw_toName(v___x_3791_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v___x_3793_; 
v___x_3793_ = lean_box(0);
return v___x_3793_;
}
else
{
lean_object* v___x_3794_; 
v___x_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3792_);
return v___x_3794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3795_){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3797_ = l_Lean_Syntax_isLit_x3f(v___x_3796_, v_stx_3795_);
if (lean_obj_tag(v___x_3797_) == 1)
{
lean_object* v_val_3798_; lean_object* v___x_3799_; 
v_val_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_val_3798_);
lean_dec_ref_known(v___x_3797_, 1);
v___x_3799_ = l_Lean_Syntax_decodeNameLit(v_val_3798_);
return v___x_3799_;
}
else
{
lean_object* v___x_3800_; 
lean_dec(v___x_3797_);
v___x_3800_ = lean_box(0);
return v___x_3800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3801_);
lean_dec(v_stx_3801_);
return v_res_3802_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3803_){
_start:
{
if (lean_obj_tag(v_x_3803_) == 1)
{
lean_object* v_args_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
v_args_3804_ = lean_ctor_get(v_x_3803_, 2);
v___x_3805_ = lean_unsigned_to_nat(0u);
v___x_3806_ = lean_array_get_size(v_args_3804_);
v___x_3807_ = lean_nat_dec_lt(v___x_3805_, v___x_3806_);
return v___x_3807_;
}
else
{
uint8_t v___x_3808_; 
v___x_3808_ = 0;
return v___x_3808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3809_){
_start:
{
uint8_t v_res_3810_; lean_object* v_r_3811_; 
v_res_3810_ = l_Lean_Syntax_hasArgs(v_x_3809_);
lean_dec(v_x_3809_);
v_r_3811_ = lean_box(v_res_3810_);
return v_r_3811_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3812_){
_start:
{
if (lean_obj_tag(v_x_3812_) == 2)
{
uint8_t v___x_3813_; 
v___x_3813_ = 1;
return v___x_3813_;
}
else
{
uint8_t v___x_3814_; 
v___x_3814_ = 0;
return v___x_3814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3815_){
_start:
{
uint8_t v_res_3816_; lean_object* v_r_3817_; 
v_res_3816_ = l_Lean_Syntax_isAtom(v_x_3815_);
lean_dec(v_x_3815_);
v_r_3817_ = lean_box(v_res_3816_);
return v_r_3817_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3818_, lean_object* v_x_3819_){
_start:
{
if (lean_obj_tag(v_x_3819_) == 2)
{
lean_object* v_val_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v_val_3820_ = lean_ctor_get(v_x_3819_, 1);
lean_inc_ref(v_val_3820_);
lean_dec_ref_known(v_x_3819_, 2);
v___x_3821_ = lean_string_trim(v_val_3820_);
v___x_3822_ = lean_string_trim(v_token_3818_);
v___x_3823_ = lean_string_dec_eq(v___x_3821_, v___x_3822_);
lean_dec_ref(v___x_3822_);
lean_dec_ref(v___x_3821_);
return v___x_3823_;
}
else
{
uint8_t v___x_3824_; 
lean_dec(v_x_3819_);
lean_dec_ref(v_token_3818_);
v___x_3824_ = 0;
return v___x_3824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3825_, lean_object* v_x_3826_){
_start:
{
uint8_t v_res_3827_; lean_object* v_r_3828_; 
v_res_3827_ = l_Lean_Syntax_isToken(v_token_3825_, v_x_3826_);
v_r_3828_ = lean_box(v_res_3827_);
return v_r_3828_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3829_){
_start:
{
switch(lean_obj_tag(v_stx_3829_))
{
case 1:
{
lean_object* v_kind_3830_; lean_object* v_args_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v_kind_3830_ = lean_ctor_get(v_stx_3829_, 1);
v_args_3831_ = lean_ctor_get(v_stx_3829_, 2);
v___x_3832_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3833_ = lean_name_eq(v_kind_3830_, v___x_3832_);
if (v___x_3833_ == 0)
{
return v___x_3833_;
}
else
{
lean_object* v___x_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; 
v___x_3834_ = lean_array_get_size(v_args_3831_);
v___x_3835_ = lean_unsigned_to_nat(0u);
v___x_3836_ = lean_nat_dec_eq(v___x_3834_, v___x_3835_);
return v___x_3836_;
}
}
case 0:
{
uint8_t v___x_3837_; 
v___x_3837_ = 1;
return v___x_3837_;
}
default: 
{
uint8_t v___x_3838_; 
v___x_3838_ = 0;
return v___x_3838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3839_){
_start:
{
uint8_t v_res_3840_; lean_object* v_r_3841_; 
v_res_3840_ = l_Lean_Syntax_isNone(v_stx_3839_);
lean_dec(v_stx_3839_);
v_r_3841_ = lean_box(v_res_3840_);
return v_r_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3842_){
_start:
{
lean_object* v___x_3843_; 
v___x_3843_ = l_Lean_Syntax_getOptional_x3f(v_stx_3842_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v___x_3844_; 
v___x_3844_ = lean_box(0);
return v___x_3844_;
}
else
{
lean_object* v_val_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3853_; 
v_val_3845_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3847_ = v___x_3843_;
v_isShared_3848_ = v_isSharedCheck_3853_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_val_3845_);
lean_dec(v___x_3843_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3853_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3849_; lean_object* v___x_3851_; 
v___x_3849_ = l_Lean_Syntax_getId(v_val_3845_);
lean_dec(v_val_3845_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v___x_3849_);
v___x_3851_ = v___x_3847_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3849_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3854_);
lean_dec(v_stx_3854_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3856_, lean_object* v_x_3857_){
_start:
{
if (lean_obj_tag(v_x_3857_) == 1)
{
lean_object* v_args_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; 
v_args_3858_ = lean_ctor_get(v_x_3857_, 2);
lean_inc_ref(v_p_3856_);
lean_inc_ref(v_x_3857_);
v___x_3859_ = lean_apply_1(v_p_3856_, v_x_3857_);
v___x_3860_ = lean_unbox(v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; lean_object* v___x_3862_; size_t v_sz_3863_; size_t v___x_3864_; lean_object* v___x_3865_; lean_object* v_fst_3866_; 
lean_inc_ref(v_args_3858_);
lean_dec_ref_known(v_x_3857_, 3);
v___x_3861_ = lean_box(0);
v___x_3862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3863_ = lean_array_size(v_args_3858_);
v___x_3864_ = ((size_t)0ULL);
v___x_3865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3856_, v_args_3858_, v_sz_3863_, v___x_3864_, v___x_3862_);
lean_dec_ref(v_args_3858_);
v_fst_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_fst_3866_);
lean_dec_ref(v___x_3865_);
if (lean_obj_tag(v_fst_3866_) == 0)
{
return v___x_3861_;
}
else
{
lean_object* v_val_3867_; 
v_val_3867_ = lean_ctor_get(v_fst_3866_, 0);
lean_inc(v_val_3867_);
lean_dec_ref_known(v_fst_3866_, 1);
return v_val_3867_;
}
}
else
{
lean_object* v___x_3868_; 
lean_dec_ref(v_p_3856_);
v___x_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3868_, 0, v_x_3857_);
return v___x_3868_;
}
}
else
{
lean_object* v___x_3869_; uint8_t v___x_3870_; 
lean_inc(v_x_3857_);
v___x_3869_ = lean_apply_1(v_p_3856_, v_x_3857_);
v___x_3870_ = lean_unbox(v___x_3869_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; 
lean_dec(v_x_3857_);
v___x_3871_ = lean_box(0);
return v___x_3871_;
}
else
{
lean_object* v___x_3872_; 
v___x_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3872_, 0, v_x_3857_);
return v___x_3872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3873_, lean_object* v_as_3874_, size_t v_sz_3875_, size_t v_i_3876_, lean_object* v_b_3877_){
_start:
{
uint8_t v___x_3878_; 
v___x_3878_ = lean_usize_dec_lt(v_i_3876_, v_sz_3875_);
if (v___x_3878_ == 0)
{
lean_dec_ref(v_p_3873_);
lean_inc_ref(v_b_3877_);
return v_b_3877_;
}
else
{
lean_object* v___x_3879_; lean_object* v_a_3880_; lean_object* v___x_3881_; 
v___x_3879_ = lean_box(0);
v_a_3880_ = lean_array_uget_borrowed(v_as_3874_, v_i_3876_);
lean_inc(v_a_3880_);
lean_inc_ref(v_p_3873_);
v___x_3881_ = l_Lean_Syntax_findAux(v_p_3873_, v_a_3880_);
if (lean_obj_tag(v___x_3881_) == 1)
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
lean_dec_ref(v_p_3873_);
v___x_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
v___x_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
lean_ctor_set(v___x_3883_, 1, v___x_3879_);
return v___x_3883_;
}
else
{
lean_object* v___x_3884_; size_t v___x_3885_; size_t v___x_3886_; 
lean_dec(v___x_3881_);
v___x_3884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3885_ = ((size_t)1ULL);
v___x_3886_ = lean_usize_add(v_i_3876_, v___x_3885_);
v_i_3876_ = v___x_3886_;
v_b_3877_ = v___x_3884_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3888_, lean_object* v_as_3889_, lean_object* v_sz_3890_, lean_object* v_i_3891_, lean_object* v_b_3892_){
_start:
{
size_t v_sz_boxed_3893_; size_t v_i_boxed_3894_; lean_object* v_res_3895_; 
v_sz_boxed_3893_ = lean_unbox_usize(v_sz_3890_);
lean_dec(v_sz_3890_);
v_i_boxed_3894_ = lean_unbox_usize(v_i_3891_);
lean_dec(v_i_3891_);
v_res_3895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3888_, v_as_3889_, v_sz_boxed_3893_, v_i_boxed_3894_, v_b_3892_);
lean_dec_ref(v_b_3892_);
lean_dec_ref(v_as_3889_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3896_, lean_object* v_p_3897_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l_Lean_Syntax_findAux(v_p_3897_, v_stx_3896_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3899_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_Syntax_isNatLit_x3f(v_s_3899_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v___x_3901_; 
v___x_3901_ = lean_unsigned_to_nat(0u);
return v___x_3901_;
}
else
{
lean_object* v_val_3902_; 
v_val_3902_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_val_3902_);
lean_dec_ref_known(v___x_3900_, 1);
return v_val_3902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Lean_TSyntax_getNat(v_s_3903_);
lean_dec(v_s_3903_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3908_){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3910_ = l_Lean_Syntax_isLit_x3f(v___x_3909_, v_stx_3908_);
if (lean_obj_tag(v___x_3910_) == 1)
{
lean_object* v_val_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v_val_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_val_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v___x_3912_ = lean_unsigned_to_nat(0u);
v___x_3913_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3911_, v___x_3912_, v___x_3912_);
lean_dec(v_val_3911_);
return v___x_3913_;
}
else
{
lean_object* v___x_3914_; 
lean_dec(v___x_3910_);
v___x_3914_ = lean_box(0);
return v___x_3914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3915_);
lean_dec(v_stx_3915_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3917_){
_start:
{
lean_object* v___x_3918_; 
v___x_3918_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3917_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v___x_3919_; 
v___x_3919_ = lean_unsigned_to_nat(0u);
return v___x_3919_;
}
else
{
lean_object* v_val_3920_; 
v_val_3920_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_val_3920_);
lean_dec_ref_known(v___x_3918_, 1);
return v_val_3920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l_Lean_TSyntax_getHexNumVal(v_s_3921_);
lean_dec(v_s_3921_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3923_, lean_object* v_p_3924_, lean_object* v_n_3925_){
_start:
{
uint8_t v___x_3926_; 
v___x_3926_ = lean_string_utf8_at_end(v_s_3923_, v_p_3924_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3927_; uint32_t v___x_3928_; uint32_t v___x_3929_; uint8_t v___x_3930_; 
v___x_3927_ = lean_string_utf8_next(v_s_3923_, v_p_3924_);
v___x_3928_ = lean_string_utf8_get(v_s_3923_, v_p_3924_);
lean_dec(v_p_3924_);
v___x_3929_ = 95;
v___x_3930_ = lean_uint32_dec_eq(v___x_3928_, v___x_3929_);
if (v___x_3930_ == 0)
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3931_ = lean_unsigned_to_nat(1u);
v___x_3932_ = lean_nat_add(v_n_3925_, v___x_3931_);
lean_dec(v_n_3925_);
v_p_3924_ = v___x_3927_;
v_n_3925_ = v___x_3932_;
goto _start;
}
else
{
v_p_3924_ = v___x_3927_;
goto _start;
}
}
else
{
lean_dec(v_p_3924_);
return v_n_3925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3935_, lean_object* v_p_3936_, lean_object* v_n_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3935_, v_p_3936_, v_n_3937_);
lean_dec_ref(v_s_3935_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3939_){
_start:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3940_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3941_ = l_Lean_Syntax_isLit_x3f(v___x_3940_, v_s_3939_);
if (lean_obj_tag(v___x_3941_) == 1)
{
lean_object* v_val_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v_val_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_val_3942_);
lean_dec_ref_known(v___x_3941_, 1);
v___x_3943_ = lean_unsigned_to_nat(0u);
v___x_3944_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3942_, v___x_3943_, v___x_3943_);
lean_dec(v_val_3942_);
return v___x_3944_;
}
else
{
lean_object* v___x_3945_; 
lean_dec(v___x_3941_);
v___x_3945_ = lean_unsigned_to_nat(0u);
return v___x_3945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Lean_TSyntax_getHexNumSize(v_s_3946_);
lean_dec(v_s_3946_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3948_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_Syntax_getId(v_s_3948_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Lean_TSyntax_getId(v_s_3950_);
lean_dec(v_s_3950_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_3959_){
_start:
{
lean_object* v___x_3960_; 
v___x_3960_ = l_Lean_Syntax_isScientificLit_x3f(v_s_3959_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v___x_3961_; 
v___x_3961_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
return v___x_3961_;
}
else
{
lean_object* v_val_3962_; 
v_val_3962_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_val_3962_);
lean_dec_ref_known(v___x_3960_, 1);
return v_val_3962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lean_TSyntax_getScientific(v_s_3963_);
lean_dec(v_s_3963_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_3965_){
_start:
{
lean_object* v___x_3966_; 
v___x_3966_ = l_Lean_Syntax_isStrLit_x3f(v_s_3965_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v___x_3967_; 
v___x_3967_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_3967_;
}
else
{
lean_object* v_val_3968_; 
v_val_3968_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_val_3968_);
lean_dec_ref_known(v___x_3966_, 1);
return v_val_3968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_Lean_TSyntax_getString(v_s_3969_);
lean_dec(v_s_3969_);
return v_res_3970_;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_3971_){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = l_Lean_Syntax_isCharLit_x3f(v_s_3971_);
if (lean_obj_tag(v___x_3972_) == 0)
{
uint32_t v___x_3973_; 
v___x_3973_ = 65;
return v___x_3973_;
}
else
{
lean_object* v_val_3974_; uint32_t v___x_3975_; 
v_val_3974_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_val_3974_);
lean_dec_ref_known(v___x_3972_, 1);
v___x_3975_ = lean_unbox_uint32(v_val_3974_);
lean_dec(v_val_3974_);
return v___x_3975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_3976_){
_start:
{
uint32_t v_res_3977_; lean_object* v_r_3978_; 
v_res_3977_ = l_Lean_TSyntax_getChar(v_s_3976_);
lean_dec(v_s_3976_);
v_r_3978_ = lean_box_uint32(v_res_3977_);
return v_r_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_3979_){
_start:
{
lean_object* v___x_3980_; 
v___x_3980_ = l_Lean_Syntax_isNameLit_x3f(v_s_3979_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v___x_3981_; 
v___x_3981_ = lean_box(0);
return v___x_3981_;
}
else
{
lean_object* v_val_3982_; 
v_val_3982_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_val_3982_);
lean_dec_ref_known(v___x_3980_, 1);
return v_val_3982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Lean_TSyntax_getName(v_s_3983_);
lean_dec(v_s_3983_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_3985_){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3986_ = lean_unsigned_to_nat(0u);
v___x_3987_ = l_Lean_Syntax_getArg(v_s_3985_, v___x_3986_);
v___x_3988_ = l_Lean_Syntax_getId(v___x_3987_);
lean_dec(v___x_3987_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_TSyntax_getHygieneInfo(v_s_3989_);
lean_dec(v_s_3989_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_3991_, lean_object* v_a_3992_){
_start:
{
lean_object* v___x_3993_; 
v___x_3993_ = l_Lean_Syntax_SepArray_ofElems(v_sep_3991_, v_a_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_3994_, v_a_3995_);
lean_dec_ref(v_a_3995_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_3997_){
_start:
{
lean_object* v___f_3998_; 
v___f_3998_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3998_, 0, v_sep_3997_);
return v___f_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_3999_, lean_object* v_sep_4000_){
_start:
{
lean_object* v___f_4001_; 
v___f_4001_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4001_, 0, v_sep_4000_);
return v___f_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_4002_, lean_object* v_sep_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_4002_, v_sep_4003_);
lean_dec(v_k_4002_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_4005_, lean_object* v_val_4006_, uint8_t v_canonical_4007_){
_start:
{
lean_object* v___x_4008_; lean_object* v_src_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v_imported_4012_; lean_object* v_ctx_4013_; lean_object* v_scopes_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4030_; 
v___x_4008_ = lean_unsigned_to_nat(0u);
v_src_4009_ = l_Lean_Syntax_getArg(v_s_4005_, v___x_4008_);
v___x_4010_ = l_Lean_Syntax_getId(v_src_4009_);
v___x_4011_ = l_Lean_extractMacroScopes(v___x_4010_);
v_imported_4012_ = lean_ctor_get(v___x_4011_, 1);
v_ctx_4013_ = lean_ctor_get(v___x_4011_, 2);
v_scopes_4014_ = lean_ctor_get(v___x_4011_, 3);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4030_ == 0)
{
lean_object* v_unused_4031_; 
v_unused_4031_ = lean_ctor_get(v___x_4011_, 0);
lean_dec(v_unused_4031_);
v___x_4016_ = v___x_4011_;
v_isShared_4017_ = v_isSharedCheck_4030_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_scopes_4014_);
lean_inc(v_ctx_4013_);
lean_inc(v_imported_4012_);
lean_dec(v___x_4011_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4030_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4018_; lean_object* v___x_4020_; 
v___x_4018_ = l_Lean_Name_eraseMacroScopes(v_val_4006_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v___x_4018_);
v___x_4020_ = v___x_4016_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4018_);
lean_ctor_set(v_reuseFailAlloc_4029_, 1, v_imported_4012_);
lean_ctor_set(v_reuseFailAlloc_4029_, 2, v_ctx_4013_);
lean_ctor_set(v_reuseFailAlloc_4029_, 3, v_scopes_4014_);
v___x_4020_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
lean_object* v_id_4021_; lean_object* v___x_4022_; uint8_t v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v_id_4021_ = l_Lean_MacroScopesView_review(v___x_4020_);
v___x_4022_ = l_Lean_SourceInfo_fromRef(v_src_4009_, v_canonical_4007_);
lean_dec(v_src_4009_);
v___x_4023_ = 1;
v___x_4024_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_4006_, v___x_4023_);
v___x_4025_ = lean_string_utf8_byte_size(v___x_4024_);
v___x_4026_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4024_);
lean_ctor_set(v___x_4026_, 1, v___x_4008_);
lean_ctor_set(v___x_4026_, 2, v___x_4025_);
v___x_4027_ = lean_box(0);
v___x_4028_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4022_);
lean_ctor_set(v___x_4028_, 1, v___x_4026_);
lean_ctor_set(v___x_4028_, 2, v_id_4021_);
lean_ctor_set(v___x_4028_, 3, v___x_4027_);
return v___x_4028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_4032_, lean_object* v_val_4033_, lean_object* v_canonical_4034_){
_start:
{
uint8_t v_canonical_boxed_4035_; lean_object* v_res_4036_; 
v_canonical_boxed_4035_ = lean_unbox(v_canonical_4034_);
v_res_4036_ = l_Lean_HygieneInfo_mkIdent(v_s_4032_, v_val_4033_, v_canonical_boxed_4035_);
lean_dec(v_s_4032_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_4037_, lean_object* v_inst_4038_, lean_object* v_a_4039_){
_start:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4040_ = lean_apply_1(v_inst_4037_, v_a_4039_);
v___x_4041_ = lean_apply_1(v_inst_4038_, v___x_4040_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_4042_, lean_object* v_inst_4043_){
_start:
{
lean_object* v___f_4044_; 
v___f_4044_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4044_, 0, v_inst_4042_);
lean_closure_set(v___f_4044_, 1, v_inst_4043_);
return v___f_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_4045_, lean_object* v_k_4046_, lean_object* v_k_x27_4047_, lean_object* v_inst_4048_, lean_object* v_inst_4049_){
_start:
{
lean_object* v___f_4050_; 
v___f_4050_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4050_, 0, v_inst_4048_);
lean_closure_set(v___f_4050_, 1, v_inst_4049_);
return v___f_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_4051_, lean_object* v_k_4052_, lean_object* v_k_x27_4053_, lean_object* v_inst_4054_, lean_object* v_inst_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_4051_, v_k_4052_, v_k_x27_4053_, v_inst_4054_, v_inst_4055_);
lean_dec(v_k_x27_4053_);
lean_dec(v_k_4052_);
return v_res_4056_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4065_ = l_Lean_mkCIdent(v___x_4064_);
return v___x_4065_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4070_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4071_ = l_Lean_mkCIdent(v___x_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4072_){
_start:
{
if (v_x_4072_ == 0)
{
lean_object* v___x_4073_; 
v___x_4073_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4073_;
}
else
{
lean_object* v___x_4074_; 
v___x_4074_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4075_){
_start:
{
uint8_t v_x_85__boxed_4076_; lean_object* v_res_4077_; 
v_x_85__boxed_4076_ = lean_unbox(v_x_4075_);
v_res_4077_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4076_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4080_){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4081_ = lean_box(2);
v___x_4082_ = l_Lean_Syntax_mkCharLit(v_val_4080_, v___x_4081_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4083_){
_start:
{
uint32_t v_val_boxed_4084_; lean_object* v_res_4085_; 
v_val_boxed_4084_ = lean_unbox_uint32(v_val_4083_);
lean_dec(v_val_4083_);
v_res_4085_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4084_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4088_){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4089_ = lean_box(2);
v___x_4090_ = l_Lean_Syntax_mkStrLit(v_val_4088_, v___x_4089_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4093_){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4094_ = l_Nat_reprFast(v_n_4093_);
v___x_4095_ = lean_box(2);
v___x_4096_ = l_Lean_Syntax_mkNumLit(v___x_4094_, v___x_4095_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4104_){
_start:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4105_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4106_ = lean_substring_tostring(v_s_4104_);
v___x_4107_ = lean_box(2);
v___x_4108_ = l_Lean_Syntax_mkStrLit(v___x_4106_, v___x_4107_);
v___x_4109_ = lean_unsigned_to_nat(1u);
v___x_4110_ = lean_mk_empty_array_with_capacity(v___x_4109_);
v___x_4111_ = lean_array_push(v___x_4110_, v___x_4108_);
v___x_4112_ = l_Lean_Syntax_mkCApp(v___x_4105_, v___x_4111_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4115_, lean_object* v_x_4116_){
_start:
{
switch(lean_obj_tag(v_x_4116_))
{
case 0:
{
uint8_t v___x_4117_; 
v___x_4117_ = l_List_isEmpty___redArg(v_acc_4115_);
if (v___x_4117_ == 0)
{
lean_object* v___x_4118_; 
v___x_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4118_, 0, v_acc_4115_);
return v___x_4118_;
}
else
{
lean_object* v___x_4119_; 
lean_dec(v_acc_4115_);
v___x_4119_ = lean_box(0);
return v___x_4119_;
}
}
case 1:
{
lean_object* v_pre_4120_; lean_object* v_str_4121_; lean_object* v_val_4123_; lean_object* v___x_4126_; lean_object* v___x_4127_; uint8_t v___x_4128_; 
v_pre_4120_ = lean_ctor_get(v_x_4116_, 0);
lean_inc(v_pre_4120_);
v_str_4121_ = lean_ctor_get(v_x_4116_, 1);
lean_inc_ref(v_str_4121_);
lean_dec_ref_known(v_x_4116_, 2);
v___x_4126_ = lean_unsigned_to_nat(0u);
v___x_4127_ = lean_string_utf8_byte_size(v_str_4121_);
v___x_4128_ = lean_nat_dec_lt(v___x_4126_, v___x_4127_);
if (v___x_4128_ == 0)
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4129_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4130_ = lean_string_append(v___x_4129_, v_str_4121_);
lean_dec_ref(v_str_4121_);
v___x_4131_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4132_ = lean_string_append(v___x_4130_, v___x_4131_);
v_val_4123_ = v___x_4132_;
goto v___jp_4122_;
}
else
{
lean_object* v___f_4133_; uint8_t v___y_4135_; lean_object* v___f_4142_; uint32_t v___y_4149_; uint32_t v___y_4154_; uint8_t v___y_4155_; uint8_t v_c_4169_; uint8_t v___x_4178_; uint8_t v___x_4179_; 
v___f_4133_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v___f_4142_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_4169_ = lean_string_get_byte_fast(v_str_4121_, v___x_4126_);
v___x_4178_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_4179_ = lean_uint8_dec_le(v___x_4178_, v_c_4169_);
if (v___x_4179_ == 0)
{
goto v___jp_4173_;
}
else
{
uint8_t v___x_4180_; uint8_t v___x_4181_; 
v___x_4180_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_4181_ = lean_uint8_dec_le(v_c_4169_, v___x_4180_);
if (v___x_4181_ == 0)
{
goto v___jp_4173_;
}
else
{
goto v___jp_4166_;
}
}
v___jp_4134_:
{
if (v___y_4135_ == 0)
{
uint8_t v___x_4136_; 
lean_inc_ref(v_str_4121_);
v___x_4136_ = lean_string_any(v_str_4121_, v___f_4133_);
if (v___x_4136_ == 0)
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4137_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4138_ = lean_string_append(v___x_4137_, v_str_4121_);
lean_dec_ref(v_str_4121_);
v___x_4139_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4140_ = lean_string_append(v___x_4138_, v___x_4139_);
v_val_4123_ = v___x_4140_;
goto v___jp_4122_;
}
else
{
lean_object* v___x_4141_; 
lean_dec_ref(v_str_4121_);
lean_dec(v_pre_4120_);
lean_dec(v_acc_4115_);
v___x_4141_ = lean_box(0);
return v___x_4141_;
}
}
else
{
v_val_4123_ = v_str_4121_;
goto v___jp_4122_;
}
}
v___jp_4143_:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; uint8_t v___x_4147_; 
lean_inc_ref(v_str_4121_);
v___x_4144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4144_, 0, v_str_4121_);
lean_ctor_set(v___x_4144_, 1, v___x_4126_);
lean_ctor_set(v___x_4144_, 2, v___x_4127_);
v___x_4145_ = lean_unsigned_to_nat(1u);
v___x_4146_ = lean_substring_drop(v___x_4144_, v___x_4145_);
v___x_4147_ = lean_substring_all(v___x_4146_, v___f_4142_);
v___y_4135_ = v___x_4147_;
goto v___jp_4134_;
}
v___jp_4148_:
{
uint32_t v___x_4150_; uint8_t v___x_4151_; 
v___x_4150_ = 95;
v___x_4151_ = lean_uint32_dec_eq(v___y_4149_, v___x_4150_);
if (v___x_4151_ == 0)
{
uint8_t v___x_4152_; 
v___x_4152_ = l_Lean_isLetterLike(v___y_4149_);
if (v___x_4152_ == 0)
{
v___y_4135_ = v___x_4152_;
goto v___jp_4134_;
}
else
{
goto v___jp_4143_;
}
}
else
{
goto v___jp_4143_;
}
}
v___jp_4153_:
{
if (v___y_4155_ == 0)
{
uint32_t v___x_4156_; uint8_t v___x_4157_; 
v___x_4156_ = 97;
v___x_4157_ = lean_uint32_dec_le(v___x_4156_, v___y_4154_);
if (v___x_4157_ == 0)
{
v___y_4149_ = v___y_4154_;
goto v___jp_4148_;
}
else
{
uint32_t v___x_4158_; uint8_t v___x_4159_; 
v___x_4158_ = 122;
v___x_4159_ = lean_uint32_dec_le(v___y_4154_, v___x_4158_);
if (v___x_4159_ == 0)
{
v___y_4149_ = v___y_4154_;
goto v___jp_4148_;
}
else
{
goto v___jp_4143_;
}
}
}
else
{
goto v___jp_4143_;
}
}
v___jp_4160_:
{
uint32_t v___x_4161_; uint32_t v___x_4162_; uint8_t v___x_4163_; 
v___x_4161_ = lean_string_utf8_get(v_str_4121_, v___x_4126_);
v___x_4162_ = 65;
v___x_4163_ = lean_uint32_dec_le(v___x_4162_, v___x_4161_);
if (v___x_4163_ == 0)
{
v___y_4154_ = v___x_4161_;
v___y_4155_ = v___x_4163_;
goto v___jp_4153_;
}
else
{
uint32_t v___x_4164_; uint8_t v___x_4165_; 
v___x_4164_ = 90;
v___x_4165_ = lean_uint32_dec_le(v___x_4161_, v___x_4164_);
v___y_4154_ = v___x_4161_;
v___y_4155_ = v___x_4165_;
goto v___jp_4153_;
}
}
v___jp_4166_:
{
lean_object* v___x_4167_; uint8_t v___x_4168_; 
v___x_4167_ = lean_unsigned_to_nat(1u);
v___x_4168_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4121_, v___x_4167_);
if (v___x_4168_ == 0)
{
goto v___jp_4160_;
}
else
{
v___y_4135_ = v___x_4168_;
goto v___jp_4134_;
}
}
v___jp_4170_:
{
uint8_t v___x_4171_; uint8_t v___x_4172_; 
v___x_4171_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_4172_ = lean_uint8_dec_eq(v_c_4169_, v___x_4171_);
if (v___x_4172_ == 0)
{
goto v___jp_4160_;
}
else
{
goto v___jp_4166_;
}
}
v___jp_4173_:
{
uint8_t v___x_4174_; uint8_t v___x_4175_; 
v___x_4174_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_4175_ = lean_uint8_dec_le(v___x_4174_, v_c_4169_);
if (v___x_4175_ == 0)
{
goto v___jp_4170_;
}
else
{
uint8_t v___x_4176_; uint8_t v___x_4177_; 
v___x_4176_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_4177_ = lean_uint8_dec_le(v_c_4169_, v___x_4176_);
if (v___x_4177_ == 0)
{
goto v___jp_4170_;
}
else
{
goto v___jp_4166_;
}
}
}
}
v___jp_4122_:
{
lean_object* v___x_4124_; 
v___x_4124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4124_, 0, v_val_4123_);
lean_ctor_set(v___x_4124_, 1, v_acc_4115_);
v_acc_4115_ = v___x_4124_;
v_x_4116_ = v_pre_4120_;
goto _start;
}
}
default: 
{
lean_object* v___x_4182_; 
lean_dec_ref_known(v_x_4116_, 2);
lean_dec(v_acc_4115_);
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
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t v___x_4430_, lean_object* v_k_4431_){
_start:
{
lean_object* v___x_4432_; uint8_t v___x_4433_; 
v___x_4432_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_4433_ = lean_name_eq(v_k_4431_, v___x_4432_);
if (v___x_4433_ == 0)
{
uint8_t v___x_4434_; 
v___x_4434_ = 1;
return v___x_4434_;
}
else
{
return v___x_4430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v___x_4435_, lean_object* v_k_4436_){
_start:
{
uint8_t v___x_442__boxed_4437_; uint8_t v_res_4438_; lean_object* v_r_4439_; 
v___x_442__boxed_4437_ = lean_unbox(v___x_4435_);
v_res_4438_ = l_Lean_evalPrec___lam__0(v___x_442__boxed_4437_, v_k_4436_);
lean_dec(v_k_4436_);
v_r_4439_ = lean_box(v_res_4438_);
return v_r_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_){
_start:
{
lean_object* v_methods_4444_; lean_object* v_quotContext_4445_; lean_object* v_currMacroScope_4446_; lean_object* v_currRecDepth_4447_; lean_object* v_maxRecDepth_4448_; lean_object* v_ref_4449_; uint8_t v___x_4450_; 
v_methods_4444_ = lean_ctor_get(v_a_4442_, 0);
v_quotContext_4445_ = lean_ctor_get(v_a_4442_, 1);
v_currMacroScope_4446_ = lean_ctor_get(v_a_4442_, 2);
v_currRecDepth_4447_ = lean_ctor_get(v_a_4442_, 3);
v_maxRecDepth_4448_ = lean_ctor_get(v_a_4442_, 4);
v_ref_4449_ = lean_ctor_get(v_a_4442_, 5);
v___x_4450_ = lean_nat_dec_eq(v_currRecDepth_4447_, v_maxRecDepth_4448_);
if (v___x_4450_ == 0)
{
lean_object* v___x_4451_; lean_object* v___f_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4451_ = lean_box(v___x_4450_);
v___f_4452_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4452_, 0, v___x_4451_);
v___x_4453_ = lean_unsigned_to_nat(1u);
v___x_4454_ = lean_nat_add(v_currRecDepth_4447_, v___x_4453_);
lean_inc(v_ref_4449_);
lean_inc(v_maxRecDepth_4448_);
lean_inc(v_currMacroScope_4446_);
lean_inc(v_quotContext_4445_);
lean_inc(v_methods_4444_);
v___x_4455_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4455_, 0, v_methods_4444_);
lean_ctor_set(v___x_4455_, 1, v_quotContext_4445_);
lean_ctor_set(v___x_4455_, 2, v_currMacroScope_4446_);
lean_ctor_set(v___x_4455_, 3, v___x_4454_);
lean_ctor_set(v___x_4455_, 4, v_maxRecDepth_4448_);
lean_ctor_set(v___x_4455_, 5, v_ref_4449_);
lean_inc_ref(v___x_4455_);
v___x_4456_ = l_Lean_expandMacros(v_stx_4441_, v___f_4452_, v___x_4455_, v_a_4443_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v_a_4457_; lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4470_; 
v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
v_a_4458_ = lean_ctor_get(v___x_4456_, 1);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4460_ = v___x_4456_;
v_isShared_4461_ = v_isSharedCheck_4470_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_inc(v_a_4457_);
lean_dec(v___x_4456_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4470_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4462_; uint8_t v___x_4463_; 
v___x_4462_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4457_);
v___x_4463_ = l_Lean_Syntax_isOfKind(v_a_4457_, v___x_4462_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4464_; lean_object* v___x_4465_; 
lean_del_object(v___x_4460_);
v___x_4464_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4465_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4457_, v___x_4464_, v___x_4455_, v_a_4458_);
lean_dec_ref_known(v___x_4455_, 6);
lean_dec(v_a_4457_);
return v___x_4465_;
}
else
{
lean_object* v___x_4466_; lean_object* v___x_4468_; 
lean_dec_ref_known(v___x_4455_, 6);
v___x_4466_ = l_Lean_TSyntax_getNat(v_a_4457_);
lean_dec(v_a_4457_);
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 0, v___x_4466_);
v___x_4468_ = v___x_4460_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4466_);
lean_ctor_set(v_reuseFailAlloc_4469_, 1, v_a_4458_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
else
{
lean_object* v_a_4471_; lean_object* v_a_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4479_; 
lean_dec_ref_known(v___x_4455_, 6);
v_a_4471_ = lean_ctor_get(v___x_4456_, 0);
v_a_4472_ = lean_ctor_get(v___x_4456_, 1);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4474_ = v___x_4456_;
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_a_4472_);
lean_inc(v_a_4471_);
lean_dec(v___x_4456_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4477_; 
if (v_isShared_4475_ == 0)
{
v___x_4477_ = v___x_4474_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_a_4471_);
lean_ctor_set(v_reuseFailAlloc_4478_, 1, v_a_4472_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
}
else
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4480_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4481_, 0, v_stx_4441_);
lean_ctor_set(v___x_4481_, 1, v___x_4480_);
v___x_4482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4481_);
lean_ctor_set(v___x_4482_, 1, v_a_4443_);
return v___x_4482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object* v_stx_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_Lean_evalPrec(v_stx_4483_, v_a_4484_, v_a_4485_);
lean_dec_ref(v_a_4484_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_){
_start:
{
lean_object* v_methods_4491_; lean_object* v_quotContext_4492_; lean_object* v_currMacroScope_4493_; lean_object* v_currRecDepth_4494_; lean_object* v_maxRecDepth_4495_; lean_object* v_ref_4496_; uint8_t v___x_4497_; 
v_methods_4491_ = lean_ctor_get(v_a_4489_, 0);
v_quotContext_4492_ = lean_ctor_get(v_a_4489_, 1);
v_currMacroScope_4493_ = lean_ctor_get(v_a_4489_, 2);
v_currRecDepth_4494_ = lean_ctor_get(v_a_4489_, 3);
v_maxRecDepth_4495_ = lean_ctor_get(v_a_4489_, 4);
v_ref_4496_ = lean_ctor_get(v_a_4489_, 5);
v___x_4497_ = lean_nat_dec_eq(v_currRecDepth_4494_, v_maxRecDepth_4495_);
if (v___x_4497_ == 0)
{
lean_object* v___x_4498_; lean_object* v___f_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4498_ = lean_box(v___x_4497_);
v___f_4499_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4499_, 0, v___x_4498_);
v___x_4500_ = lean_unsigned_to_nat(1u);
v___x_4501_ = lean_nat_add(v_currRecDepth_4494_, v___x_4500_);
lean_inc(v_ref_4496_);
lean_inc(v_maxRecDepth_4495_);
lean_inc(v_currMacroScope_4493_);
lean_inc(v_quotContext_4492_);
lean_inc(v_methods_4491_);
v___x_4502_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4502_, 0, v_methods_4491_);
lean_ctor_set(v___x_4502_, 1, v_quotContext_4492_);
lean_ctor_set(v___x_4502_, 2, v_currMacroScope_4493_);
lean_ctor_set(v___x_4502_, 3, v___x_4501_);
lean_ctor_set(v___x_4502_, 4, v_maxRecDepth_4495_);
lean_ctor_set(v___x_4502_, 5, v_ref_4496_);
lean_inc_ref(v___x_4502_);
v___x_4503_ = l_Lean_expandMacros(v_stx_4488_, v___f_4499_, v___x_4502_, v_a_4490_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; lean_object* v_a_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4517_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
v_a_4505_ = lean_ctor_get(v___x_4503_, 1);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4507_ = v___x_4503_;
v_isShared_4508_ = v_isSharedCheck_4517_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_a_4505_);
lean_inc(v_a_4504_);
lean_dec(v___x_4503_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4517_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4509_; uint8_t v___x_4510_; 
v___x_4509_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4504_);
v___x_4510_ = l_Lean_Syntax_isOfKind(v_a_4504_, v___x_4509_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
lean_del_object(v___x_4507_);
v___x_4511_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
v___x_4512_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4504_, v___x_4511_, v___x_4502_, v_a_4505_);
lean_dec_ref_known(v___x_4502_, 6);
lean_dec(v_a_4504_);
return v___x_4512_;
}
else
{
lean_object* v___x_4513_; lean_object* v___x_4515_; 
lean_dec_ref_known(v___x_4502_, 6);
v___x_4513_ = l_Lean_TSyntax_getNat(v_a_4504_);
lean_dec(v_a_4504_);
if (v_isShared_4508_ == 0)
{
lean_ctor_set(v___x_4507_, 0, v___x_4513_);
v___x_4515_ = v___x_4507_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v___x_4513_);
lean_ctor_set(v_reuseFailAlloc_4516_, 1, v_a_4505_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
else
{
lean_object* v_a_4518_; lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec_ref_known(v___x_4502_, 6);
v_a_4518_ = lean_ctor_get(v___x_4503_, 0);
v_a_4519_ = lean_ctor_get(v___x_4503_, 1);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4503_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_inc(v_a_4518_);
lean_dec(v___x_4503_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4518_);
lean_ctor_set(v_reuseFailAlloc_4525_, 1, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
else
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4527_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4528_, 0, v_stx_4488_);
lean_ctor_set(v___x_4528_, 1, v___x_4527_);
v___x_4529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4529_, 0, v___x_4528_);
lean_ctor_set(v___x_4529_, 1, v_a_4490_);
return v___x_4529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object* v_stx_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l_Lean_evalPrio(v_stx_4530_, v_a_4531_, v_a_4532_);
lean_dec_ref(v_a_4531_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_){
_start:
{
if (lean_obj_tag(v_x_4534_) == 0)
{
lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4537_ = lean_unsigned_to_nat(1000u);
v___x_4538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4537_);
lean_ctor_set(v___x_4538_, 1, v_a_4536_);
return v___x_4538_;
}
else
{
lean_object* v_val_4539_; lean_object* v___x_4540_; 
v_val_4539_ = lean_ctor_get(v_x_4534_, 0);
lean_inc(v_val_4539_);
lean_dec_ref_known(v_x_4534_, 1);
v___x_4540_ = l_Lean_evalPrio(v_val_4539_, v_a_4535_, v_a_4536_);
return v___x_4540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object* v_x_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_evalOptPrio(v_x_4541_, v_a_4542_, v_a_4543_);
lean_dec_ref(v_a_4542_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4545_, lean_object* v_x1_4546_, lean_object* v_x2_4547_){
_start:
{
lean_object* v_fst_4548_; uint8_t v___x_4549_; 
v_fst_4548_ = lean_ctor_get(v_x1_4546_, 0);
v___x_4549_ = lean_unbox(v_fst_4548_);
if (v___x_4549_ == 0)
{
lean_object* v_snd_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4558_; 
lean_dec(v_x2_4547_);
v_snd_4550_ = lean_ctor_get(v_x1_4546_, 1);
v_isSharedCheck_4558_ = !lean_is_exclusive(v_x1_4546_);
if (v_isSharedCheck_4558_ == 0)
{
lean_object* v_unused_4559_; 
v_unused_4559_ = lean_ctor_get(v_x1_4546_, 0);
lean_dec(v_unused_4559_);
v___x_4552_ = v_x1_4546_;
v_isShared_4553_ = v_isSharedCheck_4558_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_snd_4550_);
lean_dec(v_x1_4546_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4558_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4554_; lean_object* v___x_4556_; 
v___x_4554_ = lean_box(v___x_4545_);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 0, v___x_4554_);
v___x_4556_ = v___x_4552_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4554_);
lean_ctor_set(v_reuseFailAlloc_4557_, 1, v_snd_4550_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
else
{
lean_object* v_snd_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4570_; 
v_snd_4560_ = lean_ctor_get(v_x1_4546_, 1);
v_isSharedCheck_4570_ = !lean_is_exclusive(v_x1_4546_);
if (v_isSharedCheck_4570_ == 0)
{
lean_object* v_unused_4571_; 
v_unused_4571_ = lean_ctor_get(v_x1_4546_, 0);
lean_dec(v_unused_4571_);
v___x_4562_ = v_x1_4546_;
v_isShared_4563_ = v_isSharedCheck_4570_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_snd_4560_);
lean_dec(v_x1_4546_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4570_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
uint8_t v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4568_; 
v___x_4564_ = 0;
v___x_4565_ = lean_array_push(v_snd_4560_, v_x2_4547_);
v___x_4566_ = lean_box(v___x_4564_);
if (v_isShared_4563_ == 0)
{
lean_ctor_set(v___x_4562_, 1, v___x_4565_);
lean_ctor_set(v___x_4562_, 0, v___x_4566_);
v___x_4568_ = v___x_4562_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v___x_4566_);
lean_ctor_set(v_reuseFailAlloc_4569_, 1, v___x_4565_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4572_, lean_object* v_x1_4573_, lean_object* v_x2_4574_){
_start:
{
uint8_t v___x_87__boxed_4575_; lean_object* v_res_4576_; 
v___x_87__boxed_4575_ = lean_unbox(v___x_4572_);
v_res_4576_ = l_Array_getSepElems___redArg___lam__0(v___x_87__boxed_4575_, v_x1_4573_, v_x2_4574_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4598_){
_start:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; uint8_t v___x_4603_; 
v___x_4599_ = lean_unsigned_to_nat(0u);
v___x_4600_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4601_ = lean_array_get_size(v_as_4598_);
v___x_4602_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4603_ = lean_nat_dec_lt(v___x_4599_, v___x_4601_);
if (v___x_4603_ == 0)
{
lean_dec_ref(v_as_4598_);
return v___x_4600_;
}
else
{
lean_object* v___x_4604_; lean_object* v___f_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; size_t v___x_4608_; size_t v___x_4609_; lean_object* v___x_4610_; lean_object* v_snd_4611_; 
v___x_4604_ = lean_box(v___x_4603_);
v___f_4605_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4605_, 0, v___x_4604_);
v___x_4606_ = lean_box(v___x_4603_);
v___x_4607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4606_);
lean_ctor_set(v___x_4607_, 1, v___x_4600_);
v___x_4608_ = ((size_t)0ULL);
v___x_4609_ = lean_usize_of_nat(v___x_4601_);
v___x_4610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4602_, v___f_4605_, v_as_4598_, v___x_4608_, v___x_4609_, v___x_4607_);
v_snd_4611_ = lean_ctor_get(v___x_4610_, 1);
lean_inc(v_snd_4611_);
lean_dec(v___x_4610_);
return v_snd_4611_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4612_, lean_object* v_as_4613_){
_start:
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; uint8_t v___x_4618_; 
v___x_4614_ = lean_unsigned_to_nat(0u);
v___x_4615_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4616_ = lean_array_get_size(v_as_4613_);
v___x_4617_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4618_ = lean_nat_dec_lt(v___x_4614_, v___x_4616_);
if (v___x_4618_ == 0)
{
lean_dec_ref(v_as_4613_);
return v___x_4615_;
}
else
{
lean_object* v___x_4619_; lean_object* v___f_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; size_t v___x_4623_; size_t v___x_4624_; lean_object* v___x_4625_; lean_object* v_snd_4626_; 
v___x_4619_ = lean_box(v___x_4618_);
v___f_4620_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4620_, 0, v___x_4619_);
v___x_4621_ = lean_box(v___x_4618_);
v___x_4622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4621_);
lean_ctor_set(v___x_4622_, 1, v___x_4615_);
v___x_4623_ = ((size_t)0ULL);
v___x_4624_ = lean_usize_of_nat(v___x_4616_);
v___x_4625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4617_, v___f_4620_, v_as_4613_, v___x_4623_, v___x_4624_, v___x_4622_);
v_snd_4626_ = lean_ctor_get(v___x_4625_, 1);
lean_inc(v_snd_4626_);
lean_dec(v___x_4625_);
return v_snd_4626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4627_, lean_object* v_inst_4628_, lean_object* v_a_4629_, lean_object* v_p_4630_, lean_object* v_acc_4631_, lean_object* v_stx_4632_, uint8_t v_____do__lift_4633_){
_start:
{
if (v_____do__lift_4633_ == 0)
{
lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; 
lean_dec(v_stx_4632_);
v___x_4642_ = lean_unsigned_to_nat(2u);
v___x_4643_ = lean_nat_add(v_i_4627_, v___x_4642_);
v___x_4644_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4628_, v_a_4629_, v_p_4630_, v___x_4643_, v_acc_4631_);
return v___x_4644_;
}
else
{
lean_object* v___x_4645_; lean_object* v___x_4646_; uint8_t v___x_4647_; 
v___x_4645_ = lean_array_get_size(v_acc_4631_);
v___x_4646_ = lean_unsigned_to_nat(0u);
v___x_4647_ = lean_nat_dec_eq(v___x_4645_, v___x_4646_);
if (v___x_4647_ == 0)
{
uint8_t v___x_4648_; 
v___x_4648_ = lean_nat_dec_eq(v_i_4627_, v___x_4646_);
if (v___x_4648_ == 0)
{
goto v___jp_4634_;
}
else
{
if (v___x_4647_ == 0)
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4649_ = lean_unsigned_to_nat(2u);
v___x_4650_ = lean_nat_add(v_i_4627_, v___x_4649_);
v___x_4651_ = lean_array_push(v_acc_4631_, v_stx_4632_);
v___x_4652_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4628_, v_a_4629_, v_p_4630_, v___x_4650_, v___x_4651_);
return v___x_4652_;
}
else
{
goto v___jp_4634_;
}
}
}
else
{
lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4653_ = lean_unsigned_to_nat(2u);
v___x_4654_ = lean_nat_add(v_i_4627_, v___x_4653_);
v___x_4655_ = lean_array_push(v_acc_4631_, v_stx_4632_);
v___x_4656_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4628_, v_a_4629_, v_p_4630_, v___x_4654_, v___x_4655_);
return v___x_4656_;
}
}
v___jp_4634_:
{
lean_object* v___x_4635_; lean_object* v_sepStx_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; 
v___x_4635_ = lean_nat_pred(v_i_4627_);
v_sepStx_4636_ = lean_array_fget_borrowed(v_a_4629_, v___x_4635_);
lean_dec(v___x_4635_);
v___x_4637_ = lean_unsigned_to_nat(2u);
v___x_4638_ = lean_nat_add(v_i_4627_, v___x_4637_);
lean_inc(v_sepStx_4636_);
v___x_4639_ = lean_array_push(v_acc_4631_, v_sepStx_4636_);
v___x_4640_ = lean_array_push(v___x_4639_, v_stx_4632_);
v___x_4641_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4628_, v_a_4629_, v_p_4630_, v___x_4638_, v___x_4640_);
return v___x_4641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4657_, lean_object* v_inst_4658_, lean_object* v_a_4659_, lean_object* v_p_4660_, lean_object* v_acc_4661_, lean_object* v_stx_4662_, lean_object* v_____do__lift_4663_){
_start:
{
uint8_t v_____do__lift_208__boxed_4664_; lean_object* v_res_4665_; 
v_____do__lift_208__boxed_4664_ = lean_unbox(v_____do__lift_4663_);
v_res_4665_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4657_, v_inst_4658_, v_a_4659_, v_p_4660_, v_acc_4661_, v_stx_4662_, v_____do__lift_208__boxed_4664_);
lean_dec(v_i_4657_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4666_, lean_object* v_a_4667_, lean_object* v_p_4668_, lean_object* v_i_4669_, lean_object* v_acc_4670_){
_start:
{
lean_object* v_toApplicative_4671_; lean_object* v_toBind_4672_; lean_object* v_toPure_4673_; lean_object* v___x_4674_; uint8_t v___x_4675_; 
v_toApplicative_4671_ = lean_ctor_get(v_inst_4666_, 0);
v_toBind_4672_ = lean_ctor_get(v_inst_4666_, 1);
lean_inc(v_toBind_4672_);
v_toPure_4673_ = lean_ctor_get(v_toApplicative_4671_, 1);
v___x_4674_ = lean_array_get_size(v_a_4667_);
v___x_4675_ = lean_nat_dec_lt(v_i_4669_, v___x_4674_);
if (v___x_4675_ == 0)
{
lean_object* v___x_4676_; 
lean_inc(v_toPure_4673_);
lean_dec(v_toBind_4672_);
lean_dec(v_i_4669_);
lean_dec(v_p_4668_);
lean_dec_ref(v_a_4667_);
lean_dec_ref(v_inst_4666_);
v___x_4676_ = lean_apply_2(v_toPure_4673_, lean_box(0), v_acc_4670_);
return v___x_4676_;
}
else
{
lean_object* v_stx_4677_; lean_object* v___f_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v_stx_4677_ = lean_array_fget(v_a_4667_, v_i_4669_);
lean_inc(v_stx_4677_);
lean_inc(v_p_4668_);
v___f_4678_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4678_, 0, v_i_4669_);
lean_closure_set(v___f_4678_, 1, v_inst_4666_);
lean_closure_set(v___f_4678_, 2, v_a_4667_);
lean_closure_set(v___f_4678_, 3, v_p_4668_);
lean_closure_set(v___f_4678_, 4, v_acc_4670_);
lean_closure_set(v___f_4678_, 5, v_stx_4677_);
v___x_4679_ = lean_apply_1(v_p_4668_, v_stx_4677_);
v___x_4680_ = lean_apply_4(v_toBind_4672_, lean_box(0), lean_box(0), v___x_4679_, v___f_4678_);
return v___x_4680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4681_, lean_object* v_inst_4682_, lean_object* v_a_4683_, lean_object* v_p_4684_, lean_object* v_i_4685_, lean_object* v_acc_4686_){
_start:
{
lean_object* v___x_4687_; 
v___x_4687_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4682_, v_a_4683_, v_p_4684_, v_i_4685_, v_acc_4686_);
return v___x_4687_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4688_, lean_object* v_a_4689_, lean_object* v_p_4690_){
_start:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4691_ = lean_unsigned_to_nat(0u);
v___x_4692_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4693_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4688_, v_a_4689_, v_p_4690_, v___x_4691_, v___x_4692_);
return v___x_4693_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4694_, lean_object* v_inst_4695_, lean_object* v_a_4696_, lean_object* v_p_4697_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l_Array_filterSepElemsM___redArg(v_inst_4695_, v_a_4696_, v_p_4697_);
return v___x_4698_;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4699_, lean_object* v_x_4700_){
_start:
{
lean_object* v___x_4701_; uint8_t v___x_4702_; 
v___x_4701_ = lean_apply_1(v_p_4699_, v_x_4700_);
v___x_4702_ = lean_unbox(v___x_4701_);
return v___x_4702_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4703_, lean_object* v_x_4704_){
_start:
{
uint8_t v_res_4705_; lean_object* v_r_4706_; 
v_res_4705_ = l_Array_filterSepElems___lam__0(v_p_4703_, v_x_4704_);
v_r_4706_ = lean_box(v_res_4705_);
return v_r_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4707_, lean_object* v_p_4708_, lean_object* v_i_4709_, lean_object* v_acc_4710_){
_start:
{
lean_object* v___x_4711_; uint8_t v___x_4712_; 
v___x_4711_ = lean_array_get_size(v_a_4707_);
v___x_4712_ = lean_nat_dec_lt(v_i_4709_, v___x_4711_);
if (v___x_4712_ == 0)
{
lean_dec(v_i_4709_);
lean_dec_ref(v_p_4708_);
return v_acc_4710_;
}
else
{
lean_object* v_stx_4713_; lean_object* v___x_4722_; uint8_t v___x_4723_; 
v_stx_4713_ = lean_array_fget_borrowed(v_a_4707_, v_i_4709_);
lean_inc_ref(v_p_4708_);
lean_inc(v_stx_4713_);
v___x_4722_ = lean_apply_1(v_p_4708_, v_stx_4713_);
v___x_4723_ = lean_unbox(v___x_4722_);
if (v___x_4723_ == 0)
{
lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4724_ = lean_unsigned_to_nat(2u);
v___x_4725_ = lean_nat_add(v_i_4709_, v___x_4724_);
lean_dec(v_i_4709_);
v_i_4709_ = v___x_4725_;
goto _start;
}
else
{
lean_object* v___x_4727_; lean_object* v___x_4728_; uint8_t v___x_4729_; 
v___x_4727_ = lean_array_get_size(v_acc_4710_);
v___x_4728_ = lean_unsigned_to_nat(0u);
v___x_4729_ = lean_nat_dec_eq(v___x_4727_, v___x_4728_);
if (v___x_4729_ == 0)
{
uint8_t v___x_4730_; 
v___x_4730_ = lean_nat_dec_eq(v_i_4709_, v___x_4728_);
if (v___x_4730_ == 0)
{
goto v___jp_4714_;
}
else
{
if (v___x_4729_ == 0)
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4731_ = lean_unsigned_to_nat(2u);
v___x_4732_ = lean_nat_add(v_i_4709_, v___x_4731_);
lean_dec(v_i_4709_);
lean_inc(v_stx_4713_);
v___x_4733_ = lean_array_push(v_acc_4710_, v_stx_4713_);
v_i_4709_ = v___x_4732_;
v_acc_4710_ = v___x_4733_;
goto _start;
}
else
{
goto v___jp_4714_;
}
}
}
else
{
lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4735_ = lean_unsigned_to_nat(2u);
v___x_4736_ = lean_nat_add(v_i_4709_, v___x_4735_);
lean_dec(v_i_4709_);
lean_inc(v_stx_4713_);
v___x_4737_ = lean_array_push(v_acc_4710_, v_stx_4713_);
v_i_4709_ = v___x_4736_;
v_acc_4710_ = v___x_4737_;
goto _start;
}
}
v___jp_4714_:
{
lean_object* v___x_4715_; lean_object* v_sepStx_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4715_ = lean_nat_pred(v_i_4709_);
v_sepStx_4716_ = lean_array_fget_borrowed(v_a_4707_, v___x_4715_);
lean_dec(v___x_4715_);
v___x_4717_ = lean_unsigned_to_nat(2u);
v___x_4718_ = lean_nat_add(v_i_4709_, v___x_4717_);
lean_dec(v_i_4709_);
lean_inc(v_sepStx_4716_);
v___x_4719_ = lean_array_push(v_acc_4710_, v_sepStx_4716_);
lean_inc(v_stx_4713_);
v___x_4720_ = lean_array_push(v___x_4719_, v_stx_4713_);
v_i_4709_ = v___x_4718_;
v_acc_4710_ = v___x_4720_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4739_, lean_object* v_p_4740_, lean_object* v_i_4741_, lean_object* v_acc_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4739_, v_p_4740_, v_i_4741_, v_acc_4742_);
lean_dec_ref(v_a_4739_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4744_, lean_object* v_p_4745_){
_start:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4746_ = lean_unsigned_to_nat(0u);
v___x_4747_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4748_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4744_, v_p_4745_, v___x_4746_, v___x_4747_);
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4749_, lean_object* v_p_4750_){
_start:
{
lean_object* v_res_4751_; 
v_res_4751_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4749_, v_p_4750_);
lean_dec_ref(v_a_4749_);
return v_res_4751_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4752_, lean_object* v_p_4753_){
_start:
{
lean_object* v___f_4754_; lean_object* v___x_4755_; 
v___f_4754_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4754_, 0, v_p_4753_);
v___x_4755_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4752_, v___f_4754_);
return v___x_4755_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4756_, lean_object* v_p_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l_Array_filterSepElems(v_a_4756_, v_p_4757_);
lean_dec_ref(v_a_4756_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4759_, lean_object* v_acc_4760_, lean_object* v_inst_4761_, lean_object* v_a_4762_, lean_object* v_f_4763_, lean_object* v_stx_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4759_, v_acc_4760_, v_inst_4761_, v_a_4762_, v_f_4763_, v_stx_4764_);
lean_dec(v_i_4759_);
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4766_, lean_object* v_a_4767_, lean_object* v_f_4768_, lean_object* v_i_4769_, lean_object* v_acc_4770_){
_start:
{
lean_object* v_toApplicative_4771_; lean_object* v_toBind_4772_; lean_object* v_toPure_4773_; lean_object* v___x_4774_; uint8_t v___x_4775_; 
v_toApplicative_4771_ = lean_ctor_get(v_inst_4766_, 0);
v_toBind_4772_ = lean_ctor_get(v_inst_4766_, 1);
v_toPure_4773_ = lean_ctor_get(v_toApplicative_4771_, 1);
v___x_4774_ = lean_array_get_size(v_a_4767_);
v___x_4775_ = lean_nat_dec_lt(v_i_4769_, v___x_4774_);
if (v___x_4775_ == 0)
{
lean_object* v___x_4776_; 
lean_inc(v_toPure_4773_);
lean_dec(v_i_4769_);
lean_dec(v_f_4768_);
lean_dec_ref(v_a_4767_);
lean_dec_ref(v_inst_4766_);
v___x_4776_ = lean_apply_2(v_toPure_4773_, lean_box(0), v_acc_4770_);
return v___x_4776_;
}
else
{
lean_object* v_stx_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; uint8_t v___x_4781_; 
v_stx_4777_ = lean_array_fget_borrowed(v_a_4767_, v_i_4769_);
v___x_4778_ = lean_unsigned_to_nat(2u);
v___x_4779_ = lean_nat_mod(v_i_4769_, v___x_4778_);
v___x_4780_ = lean_unsigned_to_nat(0u);
v___x_4781_ = lean_nat_dec_eq(v___x_4779_, v___x_4780_);
lean_dec(v___x_4779_);
if (v___x_4781_ == 0)
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4782_ = lean_unsigned_to_nat(1u);
v___x_4783_ = lean_nat_add(v_i_4769_, v___x_4782_);
lean_dec(v_i_4769_);
lean_inc(v_stx_4777_);
v___x_4784_ = lean_array_push(v_acc_4770_, v_stx_4777_);
v_i_4769_ = v___x_4783_;
v_acc_4770_ = v___x_4784_;
goto _start;
}
else
{
lean_object* v___f_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; 
lean_inc(v_stx_4777_);
lean_inc(v_toBind_4772_);
lean_inc(v_f_4768_);
v___f_4786_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4786_, 0, v_i_4769_);
lean_closure_set(v___f_4786_, 1, v_acc_4770_);
lean_closure_set(v___f_4786_, 2, v_inst_4766_);
lean_closure_set(v___f_4786_, 3, v_a_4767_);
lean_closure_set(v___f_4786_, 4, v_f_4768_);
v___x_4787_ = lean_apply_1(v_f_4768_, v_stx_4777_);
v___x_4788_ = lean_apply_4(v_toBind_4772_, lean_box(0), lean_box(0), v___x_4787_, v___f_4786_);
return v___x_4788_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4789_, lean_object* v_acc_4790_, lean_object* v_inst_4791_, lean_object* v_a_4792_, lean_object* v_f_4793_, lean_object* v_stx_4794_){
_start:
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
v___x_4795_ = lean_unsigned_to_nat(1u);
v___x_4796_ = lean_nat_add(v_i_4789_, v___x_4795_);
v___x_4797_ = lean_array_push(v_acc_4790_, v_stx_4794_);
v___x_4798_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4791_, v_a_4792_, v_f_4793_, v___x_4796_, v___x_4797_);
return v___x_4798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4799_, lean_object* v_inst_4800_, lean_object* v_a_4801_, lean_object* v_f_4802_, lean_object* v_i_4803_, lean_object* v_acc_4804_){
_start:
{
lean_object* v___x_4805_; 
v___x_4805_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4800_, v_a_4801_, v_f_4802_, v_i_4803_, v_acc_4804_);
return v___x_4805_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4806_, lean_object* v_a_4807_, lean_object* v_f_4808_){
_start:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; 
v___x_4809_ = lean_unsigned_to_nat(0u);
v___x_4810_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4811_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4806_, v_a_4807_, v_f_4808_, v___x_4809_, v___x_4810_);
return v___x_4811_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4812_, lean_object* v_inst_4813_, lean_object* v_a_4814_, lean_object* v_f_4815_){
_start:
{
lean_object* v___x_4816_; 
v___x_4816_ = l_Array_mapSepElemsM___redArg(v_inst_4813_, v_a_4814_, v_f_4815_);
return v___x_4816_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4817_, lean_object* v_x_4818_){
_start:
{
lean_object* v___x_4819_; 
v___x_4819_ = lean_apply_1(v_f_4817_, v_x_4818_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4820_, lean_object* v_f_4821_, lean_object* v_i_4822_, lean_object* v_acc_4823_){
_start:
{
lean_object* v___x_4824_; uint8_t v___x_4825_; 
v___x_4824_ = lean_array_get_size(v_a_4820_);
v___x_4825_ = lean_nat_dec_lt(v_i_4822_, v___x_4824_);
if (v___x_4825_ == 0)
{
lean_dec(v_i_4822_);
lean_dec_ref(v_f_4821_);
return v_acc_4823_;
}
else
{
lean_object* v_stx_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; uint8_t v___x_4830_; 
v_stx_4826_ = lean_array_fget_borrowed(v_a_4820_, v_i_4822_);
v___x_4827_ = lean_unsigned_to_nat(2u);
v___x_4828_ = lean_nat_mod(v_i_4822_, v___x_4827_);
v___x_4829_ = lean_unsigned_to_nat(0u);
v___x_4830_ = lean_nat_dec_eq(v___x_4828_, v___x_4829_);
lean_dec(v___x_4828_);
if (v___x_4830_ == 0)
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___x_4831_ = lean_unsigned_to_nat(1u);
v___x_4832_ = lean_nat_add(v_i_4822_, v___x_4831_);
lean_dec(v_i_4822_);
lean_inc(v_stx_4826_);
v___x_4833_ = lean_array_push(v_acc_4823_, v_stx_4826_);
v_i_4822_ = v___x_4832_;
v_acc_4823_ = v___x_4833_;
goto _start;
}
else
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
lean_inc_ref(v_f_4821_);
lean_inc(v_stx_4826_);
v___x_4835_ = lean_apply_1(v_f_4821_, v_stx_4826_);
v___x_4836_ = lean_unsigned_to_nat(1u);
v___x_4837_ = lean_nat_add(v_i_4822_, v___x_4836_);
lean_dec(v_i_4822_);
v___x_4838_ = lean_array_push(v_acc_4823_, v___x_4835_);
v_i_4822_ = v___x_4837_;
v_acc_4823_ = v___x_4838_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4840_, lean_object* v_f_4841_, lean_object* v_i_4842_, lean_object* v_acc_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4840_, v_f_4841_, v_i_4842_, v_acc_4843_);
lean_dec_ref(v_a_4840_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4845_, lean_object* v_f_4846_){
_start:
{
lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4847_ = lean_unsigned_to_nat(0u);
v___x_4848_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4849_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4845_, v_f_4846_, v___x_4847_, v___x_4848_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4850_, lean_object* v_f_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4850_, v_f_4851_);
lean_dec_ref(v_a_4850_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4853_, lean_object* v_f_4854_){
_start:
{
lean_object* v___f_4855_; lean_object* v___x_4856_; 
v___f_4855_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4855_, 0, v_f_4854_);
v___x_4856_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4853_, v___f_4855_);
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4857_, lean_object* v_f_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l_Array_mapSepElems(v_a_4857_, v_f_4858_);
lean_dec_ref(v_a_4857_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4860_, size_t v_i_4861_, size_t v_stop_4862_, lean_object* v_b_4863_){
_start:
{
lean_object* v___y_4865_; uint8_t v___x_4869_; 
v___x_4869_ = lean_usize_dec_eq(v_i_4861_, v_stop_4862_);
if (v___x_4869_ == 0)
{
lean_object* v_fst_4870_; uint8_t v___x_4871_; 
v_fst_4870_ = lean_ctor_get(v_b_4863_, 0);
v___x_4871_ = lean_unbox(v_fst_4870_);
if (v___x_4871_ == 0)
{
lean_object* v_snd_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4881_; 
v_snd_4872_ = lean_ctor_get(v_b_4863_, 1);
v_isSharedCheck_4881_ = !lean_is_exclusive(v_b_4863_);
if (v_isSharedCheck_4881_ == 0)
{
lean_object* v_unused_4882_; 
v_unused_4882_ = lean_ctor_get(v_b_4863_, 0);
lean_dec(v_unused_4882_);
v___x_4874_ = v_b_4863_;
v_isShared_4875_ = v_isSharedCheck_4881_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_snd_4872_);
lean_dec(v_b_4863_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4881_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
uint8_t v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4879_; 
v___x_4876_ = 1;
v___x_4877_ = lean_box(v___x_4876_);
if (v_isShared_4875_ == 0)
{
lean_ctor_set(v___x_4874_, 0, v___x_4877_);
v___x_4879_ = v___x_4874_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v___x_4877_);
lean_ctor_set(v_reuseFailAlloc_4880_, 1, v_snd_4872_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
v___y_4865_ = v___x_4879_;
goto v___jp_4864_;
}
}
}
else
{
lean_object* v_snd_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4893_; 
v_snd_4883_ = lean_ctor_get(v_b_4863_, 1);
v_isSharedCheck_4893_ = !lean_is_exclusive(v_b_4863_);
if (v_isSharedCheck_4893_ == 0)
{
lean_object* v_unused_4894_; 
v_unused_4894_ = lean_ctor_get(v_b_4863_, 0);
lean_dec(v_unused_4894_);
v___x_4885_ = v_b_4863_;
v_isShared_4886_ = v_isSharedCheck_4893_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_snd_4883_);
lean_dec(v_b_4863_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4893_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4891_; 
v___x_4887_ = lean_array_uget_borrowed(v_as_4860_, v_i_4861_);
lean_inc(v___x_4887_);
v___x_4888_ = lean_array_push(v_snd_4883_, v___x_4887_);
v___x_4889_ = lean_box(v___x_4869_);
if (v_isShared_4886_ == 0)
{
lean_ctor_set(v___x_4885_, 1, v___x_4888_);
lean_ctor_set(v___x_4885_, 0, v___x_4889_);
v___x_4891_ = v___x_4885_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4889_);
lean_ctor_set(v_reuseFailAlloc_4892_, 1, v___x_4888_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
v___y_4865_ = v___x_4891_;
goto v___jp_4864_;
}
}
}
}
else
{
return v_b_4863_;
}
v___jp_4864_:
{
size_t v___x_4866_; size_t v___x_4867_; 
v___x_4866_ = ((size_t)1ULL);
v___x_4867_ = lean_usize_add(v_i_4861_, v___x_4866_);
v_i_4861_ = v___x_4867_;
v_b_4863_ = v___y_4865_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4895_, lean_object* v_i_4896_, lean_object* v_stop_4897_, lean_object* v_b_4898_){
_start:
{
size_t v_i_boxed_4899_; size_t v_stop_boxed_4900_; lean_object* v_res_4901_; 
v_i_boxed_4899_ = lean_unbox_usize(v_i_4896_);
lean_dec(v_i_4896_);
v_stop_boxed_4900_ = lean_unbox_usize(v_stop_4897_);
lean_dec(v_stop_4897_);
v_res_4901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4895_, v_i_boxed_4899_, v_stop_boxed_4900_, v_b_4898_);
lean_dec_ref(v_as_4895_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4902_){
_start:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; uint8_t v___x_4906_; 
v___x_4903_ = lean_unsigned_to_nat(0u);
v___x_4904_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4905_ = lean_array_get_size(v_sa_4902_);
v___x_4906_ = lean_nat_dec_lt(v___x_4903_, v___x_4905_);
if (v___x_4906_ == 0)
{
return v___x_4904_;
}
else
{
lean_object* v___x_4907_; lean_object* v___x_4908_; size_t v___x_4909_; size_t v___x_4910_; lean_object* v___x_4911_; lean_object* v_snd_4912_; 
v___x_4907_ = lean_box(v___x_4906_);
v___x_4908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4907_);
lean_ctor_set(v___x_4908_, 1, v___x_4904_);
v___x_4909_ = ((size_t)0ULL);
v___x_4910_ = lean_usize_of_nat(v___x_4905_);
v___x_4911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4902_, v___x_4909_, v___x_4910_, v___x_4908_);
v_snd_4912_ = lean_ctor_get(v___x_4911_, 1);
lean_inc(v_snd_4912_);
lean_dec_ref(v___x_4911_);
return v_snd_4912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4913_);
lean_dec_ref(v_sa_4913_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4915_, lean_object* v_sa_4916_){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4916_);
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4918_, lean_object* v_sa_4919_){
_start:
{
lean_object* v_res_4920_; 
v_res_4920_ = l_Lean_Syntax_SepArray_getElems(v_sep_4918_, v_sa_4919_);
lean_dec_ref(v_sa_4919_);
lean_dec_ref(v_sep_4918_);
return v_res_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4921_){
_start:
{
lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; uint8_t v___x_4925_; 
v___x_4922_ = lean_unsigned_to_nat(0u);
v___x_4923_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4924_ = lean_array_get_size(v_sa_4921_);
v___x_4925_ = lean_nat_dec_lt(v___x_4922_, v___x_4924_);
if (v___x_4925_ == 0)
{
return v___x_4923_;
}
else
{
lean_object* v___x_4926_; lean_object* v___x_4927_; size_t v___x_4928_; size_t v___x_4929_; lean_object* v___x_4930_; lean_object* v_snd_4931_; 
v___x_4926_ = lean_box(v___x_4925_);
v___x_4927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4926_);
lean_ctor_set(v___x_4927_, 1, v___x_4923_);
v___x_4928_ = ((size_t)0ULL);
v___x_4929_ = lean_usize_of_nat(v___x_4924_);
v___x_4930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4921_, v___x_4928_, v___x_4929_, v___x_4927_);
v_snd_4931_ = lean_ctor_get(v___x_4930_, 1);
lean_inc(v_snd_4931_);
lean_dec_ref(v___x_4930_);
return v_snd_4931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4932_);
lean_dec_ref(v_sa_4932_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4934_, lean_object* v_sep_4935_, lean_object* v_sa_4936_){
_start:
{
lean_object* v___x_4937_; 
v___x_4937_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4936_);
return v___x_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4938_, lean_object* v_sep_4939_, lean_object* v_sa_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l_Lean_Syntax_TSepArray_getElems(v_k_4938_, v_sep_4939_, v_sa_4940_);
lean_dec_ref(v_sa_4940_);
lean_dec_ref(v_sep_4939_);
lean_dec(v_k_4938_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4942_, lean_object* v_sa_4943_, lean_object* v_e_4944_){
_start:
{
lean_object* v___x_4945_; lean_object* v___x_4946_; uint8_t v___x_4947_; 
v___x_4945_ = lean_array_get_size(v_sa_4943_);
v___x_4946_ = lean_unsigned_to_nat(0u);
v___x_4947_ = lean_nat_dec_eq(v___x_4945_, v___x_4946_);
if (v___x_4947_ == 0)
{
lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4948_ = l_Lean_mkAtom(v_sep_4942_);
v___x_4949_ = lean_array_push(v_sa_4943_, v___x_4948_);
v___x_4950_ = lean_array_push(v___x_4949_, v_e_4944_);
return v___x_4950_;
}
else
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
lean_dec_ref(v_sa_4943_);
lean_dec_ref(v_sep_4942_);
v___x_4951_ = lean_unsigned_to_nat(1u);
v___x_4952_ = lean_mk_empty_array_with_capacity(v___x_4951_);
v___x_4953_ = lean_array_push(v___x_4952_, v_e_4944_);
return v___x_4953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_4954_, lean_object* v_sep_4955_, lean_object* v_sa_4956_, lean_object* v_e_4957_){
_start:
{
lean_object* v___x_4958_; 
v___x_4958_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_4955_, v_sa_4956_, v_e_4957_);
return v___x_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_4959_, lean_object* v_sep_4960_, lean_object* v_sa_4961_, lean_object* v_e_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Lean_Syntax_TSepArray_push(v_k_4959_, v_sep_4960_, v_sa_4961_, v_e_4962_);
lean_dec(v_k_4959_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg(){
_start:
{
lean_object* v___x_4965_; 
v___x_4965_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg___boxed(lean_object* v___dummy_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v_res_4967_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0(void){
_start:
{
lean_object* v___x_4968_; 
v___x_4968_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_4969_){
_start:
{
lean_object* v___x_4970_; 
v___x_4970_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_4971_){
_start:
{
lean_object* v_res_4972_; 
v_res_4972_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_4971_);
lean_dec_ref(v_sep_4971_);
return v_res_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg(){
_start:
{
lean_object* v___x_4974_; 
v___x_4974_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg___boxed(lean_object* v___dummy_4975_){
_start:
{
lean_object* v_res_4976_; 
v_res_4976_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v_res_4976_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0(void){
_start:
{
lean_object* v___x_4977_; 
v___x_4977_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v___x_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_4978_, lean_object* v_k_4979_){
_start:
{
lean_object* v___x_4980_; 
v___x_4980_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_4981_, lean_object* v_k_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_4981_, v_k_4982_);
lean_dec_ref(v_k_4982_);
lean_dec(v_sep_4981_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(lean_object* v_v_4984_){
_start:
{
lean_inc_ref(v_v_4984_);
return v_v_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0___boxed(lean_object* v_v_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(v_v_4985_);
lean_dec_ref(v_v_4985_);
return v_res_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg(){
_start:
{
lean_object* v___f_4989_; 
v___f_4989_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___boxed(lean_object* v___dummy_4990_){
_start:
{
lean_object* v_res_4991_; 
v_res_4991_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg();
return v_res_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray(lean_object* v_k_4992_, lean_object* v_sep_4993_){
_start:
{
lean_object* v___f_4994_; 
v___f_4994_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___boxed(lean_object* v_k_4995_, lean_object* v_sep_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l_Lean_Syntax_instCoeOutTSepArraySepArray(v_k_4995_, v_sep_4996_);
lean_dec_ref(v_sep_4996_);
lean_dec(v_k_4995_);
return v_res_4997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_4998_, lean_object* v_sep_4999_){
_start:
{
lean_object* v___x_5000_; 
v___x_5000_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_5000_, 0, v_k_4998_);
lean_closure_set(v___x_5000_, 1, v_sep_4999_);
return v___x_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_5001_, lean_object* v_x_5002_){
_start:
{
lean_object* v___x_5003_; 
v___x_5003_ = lean_apply_1(v_inst_5001_, v_x_5002_);
return v___x_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_5004_, lean_object* v_a_5005_){
_start:
{
lean_object* v___x_5006_; size_t v_sz_5007_; size_t v___x_5008_; lean_object* v___x_5009_; 
v___x_5006_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_5007_ = lean_array_size(v_a_5005_);
v___x_5008_ = ((size_t)0ULL);
v___x_5009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5006_, v___f_5004_, v_sz_5007_, v___x_5008_, v_a_5005_);
return v___x_5009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_5010_){
_start:
{
lean_object* v___f_5011_; lean_object* v___f_5012_; 
v___f_5011_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5011_, 0, v_inst_5010_);
v___f_5012_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5012_, 0, v___f_5011_);
return v___f_5012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_5013_, lean_object* v_k_x27_5014_, lean_object* v_inst_5015_){
_start:
{
lean_object* v___x_5016_; 
v___x_5016_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_5015_);
return v___x_5016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_5017_, lean_object* v_k_x27_5018_, lean_object* v_inst_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_5017_, v_k_x27_5018_, v_inst_5019_);
lean_dec(v_k_x27_5018_);
lean_dec(v_k_5017_);
return v_res_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(lean_object* v_a_5021_){
_start:
{
lean_inc_ref(v_a_5021_);
return v_a_5021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0___boxed(lean_object* v_a_5022_){
_start:
{
lean_object* v_res_5023_; 
v_res_5023_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(v_a_5022_);
lean_dec_ref(v_a_5022_);
return v_res_5023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg(){
_start:
{
lean_object* v___f_5026_; 
v___f_5026_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_5026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___boxed(lean_object* v___dummy_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg();
return v_res_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_5029_){
_start:
{
lean_object* v___f_5030_; 
v___f_5030_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_5030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* v_k_5031_){
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(v_k_5031_);
lean_dec(v_k_5031_);
return v_res_5032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_5039_){
_start:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; 
v___x_5040_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1));
v___x_5041_ = lean_box(2);
v___x_5042_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
v___x_5043_ = lean_unsigned_to_nat(2u);
v___x_5044_ = lean_mk_empty_array_with_capacity(v___x_5043_);
v___x_5045_ = lean_array_push(v___x_5044_, v_id_5039_);
v___x_5046_ = lean_array_push(v___x_5045_, v___x_5042_);
v___x_5047_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5047_, 0, v___x_5041_);
lean_ctor_set(v___x_5047_, 1, v___x_5040_);
lean_ctor_set(v___x_5047_, 2, v___x_5046_);
return v___x_5047_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_5051_; lean_object* v___x_5052_; 
v___x_5051_ = 123;
v___x_5052_ = lean_box_uint32(v___x_5051_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* v_s_5053_, lean_object* v_i_5054_){
_start:
{
lean_object* v___x_5055_; 
v___x_5055_ = l_Lean_Syntax_decodeQuotedChar(v_s_5053_, v_i_5054_);
if (lean_obj_tag(v___x_5055_) == 0)
{
uint32_t v_c_5056_; uint32_t v___x_5057_; uint8_t v___x_5058_; 
v_c_5056_ = lean_string_utf8_get(v_s_5053_, v_i_5054_);
v___x_5057_ = 123;
v___x_5058_ = lean_uint32_dec_eq(v_c_5056_, v___x_5057_);
if (v___x_5058_ == 0)
{
return v___x_5055_;
}
else
{
lean_object* v_i_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
v_i_5059_ = lean_string_utf8_next(v_s_5053_, v_i_5054_);
v___x_5060_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
v___x_5061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5061_, 0, v___x_5060_);
lean_ctor_set(v___x_5061_, 1, v_i_5059_);
v___x_5062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5061_);
return v___x_5062_;
}
}
else
{
return v___x_5055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* v_s_5063_, lean_object* v_i_5064_){
_start:
{
lean_object* v_res_5065_; 
v_res_5065_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5063_, v_i_5064_);
lean_dec(v_i_5064_);
lean_dec_ref(v_s_5063_);
return v_res_5065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* v_s_5066_, lean_object* v_i_5067_, lean_object* v_acc_5068_){
_start:
{
uint32_t v_c_5069_; uint32_t v___x_5070_; uint8_t v___x_5071_; 
v_c_5069_ = lean_string_utf8_get(v_s_5066_, v_i_5067_);
v___x_5070_ = 34;
v___x_5071_ = lean_uint32_dec_eq(v_c_5069_, v___x_5070_);
if (v___x_5071_ == 0)
{
uint32_t v___x_5072_; uint8_t v___x_5073_; 
v___x_5072_ = 123;
v___x_5073_ = lean_uint32_dec_eq(v_c_5069_, v___x_5072_);
if (v___x_5073_ == 0)
{
lean_object* v_i_5074_; uint8_t v___x_5075_; 
v_i_5074_ = lean_string_utf8_next(v_s_5066_, v_i_5067_);
lean_dec(v_i_5067_);
v___x_5075_ = lean_string_utf8_at_end(v_s_5066_, v_i_5074_);
if (v___x_5075_ == 0)
{
uint32_t v___x_5076_; uint8_t v___x_5077_; 
v___x_5076_ = 92;
v___x_5077_ = lean_uint32_dec_eq(v_c_5069_, v___x_5076_);
if (v___x_5077_ == 0)
{
lean_object* v___x_5078_; 
v___x_5078_ = lean_string_push(v_acc_5068_, v_c_5069_);
v_i_5067_ = v_i_5074_;
v_acc_5068_ = v___x_5078_;
goto _start;
}
else
{
lean_object* v___x_5080_; 
v___x_5080_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5066_, v_i_5074_);
if (lean_obj_tag(v___x_5080_) == 1)
{
lean_object* v_val_5081_; lean_object* v_fst_5082_; lean_object* v_snd_5083_; uint32_t v___x_5084_; lean_object* v___x_5085_; 
lean_dec(v_i_5074_);
v_val_5081_ = lean_ctor_get(v___x_5080_, 0);
lean_inc(v_val_5081_);
lean_dec_ref_known(v___x_5080_, 1);
v_fst_5082_ = lean_ctor_get(v_val_5081_, 0);
lean_inc(v_fst_5082_);
v_snd_5083_ = lean_ctor_get(v_val_5081_, 1);
lean_inc(v_snd_5083_);
lean_dec(v_val_5081_);
v___x_5084_ = lean_unbox_uint32(v_fst_5082_);
lean_dec(v_fst_5082_);
v___x_5085_ = lean_string_push(v_acc_5068_, v___x_5084_);
v_i_5067_ = v_snd_5083_;
v_acc_5068_ = v___x_5085_;
goto _start;
}
else
{
lean_object* v___x_5087_; 
lean_dec(v___x_5080_);
lean_inc_ref(v_s_5066_);
v___x_5087_ = l_Lean_Syntax_decodeStringGap(v_s_5066_, v_i_5074_);
lean_dec(v_i_5074_);
if (lean_obj_tag(v___x_5087_) == 1)
{
lean_object* v_val_5088_; 
v_val_5088_ = lean_ctor_get(v___x_5087_, 0);
lean_inc(v_val_5088_);
lean_dec_ref_known(v___x_5087_, 1);
v_i_5067_ = v_val_5088_;
goto _start;
}
else
{
lean_object* v___x_5090_; 
lean_dec(v___x_5087_);
lean_dec_ref(v_acc_5068_);
lean_dec_ref(v_s_5066_);
v___x_5090_ = lean_box(0);
return v___x_5090_;
}
}
}
}
else
{
lean_object* v___x_5091_; 
lean_dec(v_i_5074_);
lean_dec_ref(v_acc_5068_);
lean_dec_ref(v_s_5066_);
v___x_5091_ = lean_box(0);
return v___x_5091_;
}
}
else
{
lean_object* v___x_5092_; 
lean_dec(v_i_5067_);
lean_dec_ref(v_s_5066_);
v___x_5092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5092_, 0, v_acc_5068_);
return v___x_5092_;
}
}
else
{
lean_object* v___x_5093_; 
lean_dec(v_i_5067_);
lean_dec_ref(v_s_5066_);
v___x_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5093_, 0, v_acc_5068_);
return v___x_5093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5094_){
_start:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5095_ = lean_unsigned_to_nat(1u);
v___x_5096_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5097_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5094_, v___x_5095_, v___x_5096_);
return v___x_5097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5101_){
_start:
{
lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___x_5102_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5103_ = l_Lean_Syntax_isLit_x3f(v___x_5102_, v_stx_5101_);
if (lean_obj_tag(v___x_5103_) == 0)
{
return v___x_5103_;
}
else
{
lean_object* v_val_5104_; lean_object* v___x_5105_; 
v_val_5104_ = lean_ctor_get(v___x_5103_, 0);
lean_inc(v_val_5104_);
lean_dec_ref_known(v___x_5103_, 1);
v___x_5105_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5104_);
return v___x_5105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5106_){
_start:
{
lean_object* v_res_5107_; 
v_res_5107_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5106_);
lean_dec(v_stx_5106_);
return v_res_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5108_){
_start:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; uint8_t v___x_5113_; 
v___x_5109_ = l_Lean_Syntax_getArgs(v_stx_5108_);
v___x_5110_ = lean_unsigned_to_nat(0u);
v___x_5111_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5112_ = lean_array_get_size(v___x_5109_);
v___x_5113_ = lean_nat_dec_lt(v___x_5110_, v___x_5112_);
if (v___x_5113_ == 0)
{
lean_dec_ref(v___x_5109_);
return v___x_5111_;
}
else
{
lean_object* v___x_5114_; lean_object* v___x_5115_; size_t v___x_5116_; size_t v___x_5117_; lean_object* v___x_5118_; lean_object* v_snd_5119_; 
v___x_5114_ = lean_box(v___x_5113_);
v___x_5115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5115_, 0, v___x_5114_);
lean_ctor_set(v___x_5115_, 1, v___x_5111_);
v___x_5116_ = ((size_t)0ULL);
v___x_5117_ = lean_usize_of_nat(v___x_5112_);
v___x_5118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5109_, v___x_5116_, v___x_5117_, v___x_5115_);
lean_dec_ref(v___x_5109_);
v_snd_5119_ = lean_ctor_get(v___x_5118_, 1);
lean_inc(v_snd_5119_);
lean_dec_ref(v___x_5118_);
return v_snd_5119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5120_){
_start:
{
lean_object* v_res_5121_; 
v_res_5121_ = l_Lean_Syntax_getSepArgs(v_stx_5120_);
lean_dec(v_stx_5120_);
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5122_, lean_object* v_mkElem_5123_, lean_object* v_mkLit_5124_, lean_object* v_as_5125_, size_t v_sz_5126_, size_t v_i_5127_, lean_object* v_b_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_){
_start:
{
lean_object* v_a_5132_; lean_object* v_a_5133_; lean_object* v_elem_5138_; lean_object* v___y_5139_; lean_object* v___y_5140_; uint8_t v___x_5145_; 
v___x_5145_ = lean_usize_dec_lt(v_i_5127_, v_sz_5126_);
if (v___x_5145_ == 0)
{
lean_object* v___x_5146_; 
lean_dec_ref(v_mkLit_5124_);
lean_dec_ref(v_mkElem_5123_);
lean_dec_ref(v_mkAppend_5122_);
v___x_5146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5146_, 0, v_b_5128_);
lean_ctor_set(v___x_5146_, 1, v___y_5130_);
return v___x_5146_;
}
else
{
lean_object* v_a_5147_; lean_object* v___x_5148_; 
v_a_5147_ = lean_array_uget_borrowed(v_as_5125_, v_i_5127_);
v___x_5148_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5147_);
if (lean_obj_tag(v___x_5148_) == 0)
{
lean_object* v_methods_5149_; lean_object* v_quotContext_5150_; lean_object* v_currMacroScope_5151_; lean_object* v_currRecDepth_5152_; lean_object* v_maxRecDepth_5153_; lean_object* v_ref_5154_; lean_object* v_ref_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; 
v_methods_5149_ = lean_ctor_get(v___y_5129_, 0);
v_quotContext_5150_ = lean_ctor_get(v___y_5129_, 1);
v_currMacroScope_5151_ = lean_ctor_get(v___y_5129_, 2);
v_currRecDepth_5152_ = lean_ctor_get(v___y_5129_, 3);
v_maxRecDepth_5153_ = lean_ctor_get(v___y_5129_, 4);
v_ref_5154_ = lean_ctor_get(v___y_5129_, 5);
v_ref_5155_ = l_Lean_replaceRef(v_a_5147_, v_ref_5154_);
lean_inc(v_maxRecDepth_5153_);
lean_inc(v_currRecDepth_5152_);
lean_inc(v_currMacroScope_5151_);
lean_inc(v_quotContext_5150_);
lean_inc(v_methods_5149_);
v___x_5156_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5156_, 0, v_methods_5149_);
lean_ctor_set(v___x_5156_, 1, v_quotContext_5150_);
lean_ctor_set(v___x_5156_, 2, v_currMacroScope_5151_);
lean_ctor_set(v___x_5156_, 3, v_currRecDepth_5152_);
lean_ctor_set(v___x_5156_, 4, v_maxRecDepth_5153_);
lean_ctor_set(v___x_5156_, 5, v_ref_5155_);
lean_inc_ref(v_mkElem_5123_);
lean_inc(v_a_5147_);
v___x_5157_ = lean_apply_3(v_mkElem_5123_, v_a_5147_, v___x_5156_, v___y_5130_);
if (lean_obj_tag(v___x_5157_) == 0)
{
lean_object* v_a_5158_; lean_object* v_a_5159_; 
v_a_5158_ = lean_ctor_get(v___x_5157_, 0);
lean_inc(v_a_5158_);
v_a_5159_ = lean_ctor_get(v___x_5157_, 1);
lean_inc(v_a_5159_);
lean_dec_ref_known(v___x_5157_, 2);
v_elem_5138_ = v_a_5158_;
v___y_5139_ = v___y_5129_;
v___y_5140_ = v_a_5159_;
goto v___jp_5137_;
}
else
{
lean_dec(v_b_5128_);
lean_dec_ref(v_mkLit_5124_);
lean_dec_ref(v_mkElem_5123_);
lean_dec_ref(v_mkAppend_5122_);
return v___x_5157_;
}
}
else
{
lean_object* v_val_5160_; uint8_t v___x_5161_; 
v_val_5160_ = lean_ctor_get(v___x_5148_, 0);
lean_inc_n(v_val_5160_, 2);
lean_dec_ref_known(v___x_5148_, 1);
v___x_5161_ = lean_string_isempty(v_val_5160_);
if (v___x_5161_ == 0)
{
lean_object* v_methods_5162_; lean_object* v_quotContext_5163_; lean_object* v_currMacroScope_5164_; lean_object* v_currRecDepth_5165_; lean_object* v_maxRecDepth_5166_; lean_object* v_ref_5167_; lean_object* v_ref_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; 
v_methods_5162_ = lean_ctor_get(v___y_5129_, 0);
v_quotContext_5163_ = lean_ctor_get(v___y_5129_, 1);
v_currMacroScope_5164_ = lean_ctor_get(v___y_5129_, 2);
v_currRecDepth_5165_ = lean_ctor_get(v___y_5129_, 3);
v_maxRecDepth_5166_ = lean_ctor_get(v___y_5129_, 4);
v_ref_5167_ = lean_ctor_get(v___y_5129_, 5);
v_ref_5168_ = l_Lean_replaceRef(v_a_5147_, v_ref_5167_);
lean_inc(v_maxRecDepth_5166_);
lean_inc(v_currRecDepth_5165_);
lean_inc(v_currMacroScope_5164_);
lean_inc(v_quotContext_5163_);
lean_inc(v_methods_5162_);
v___x_5169_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5169_, 0, v_methods_5162_);
lean_ctor_set(v___x_5169_, 1, v_quotContext_5163_);
lean_ctor_set(v___x_5169_, 2, v_currMacroScope_5164_);
lean_ctor_set(v___x_5169_, 3, v_currRecDepth_5165_);
lean_ctor_set(v___x_5169_, 4, v_maxRecDepth_5166_);
lean_ctor_set(v___x_5169_, 5, v_ref_5168_);
lean_inc_ref(v_mkLit_5124_);
v___x_5170_ = lean_apply_3(v_mkLit_5124_, v_val_5160_, v___x_5169_, v___y_5130_);
if (lean_obj_tag(v___x_5170_) == 0)
{
lean_object* v_a_5171_; lean_object* v_a_5172_; 
v_a_5171_ = lean_ctor_get(v___x_5170_, 0);
lean_inc(v_a_5171_);
v_a_5172_ = lean_ctor_get(v___x_5170_, 1);
lean_inc(v_a_5172_);
lean_dec_ref_known(v___x_5170_, 2);
v_elem_5138_ = v_a_5171_;
v___y_5139_ = v___y_5129_;
v___y_5140_ = v_a_5172_;
goto v___jp_5137_;
}
else
{
lean_dec(v_b_5128_);
lean_dec_ref(v_mkLit_5124_);
lean_dec_ref(v_mkElem_5123_);
lean_dec_ref(v_mkAppend_5122_);
return v___x_5170_;
}
}
else
{
lean_dec(v_val_5160_);
v_a_5132_ = v_b_5128_;
v_a_5133_ = v___y_5130_;
goto v___jp_5131_;
}
}
}
v___jp_5131_:
{
size_t v___x_5134_; size_t v___x_5135_; 
v___x_5134_ = ((size_t)1ULL);
v___x_5135_ = lean_usize_add(v_i_5127_, v___x_5134_);
v_i_5127_ = v___x_5135_;
v_b_5128_ = v_a_5132_;
v___y_5130_ = v_a_5133_;
goto _start;
}
v___jp_5137_:
{
uint8_t v___x_5141_; 
v___x_5141_ = l_Lean_Syntax_isMissing(v_b_5128_);
if (v___x_5141_ == 0)
{
lean_object* v___x_5142_; 
lean_inc_ref(v_mkAppend_5122_);
lean_inc_ref(v___y_5139_);
v___x_5142_ = lean_apply_4(v_mkAppend_5122_, v_b_5128_, v_elem_5138_, v___y_5139_, v___y_5140_);
if (lean_obj_tag(v___x_5142_) == 0)
{
lean_object* v_a_5143_; lean_object* v_a_5144_; 
v_a_5143_ = lean_ctor_get(v___x_5142_, 0);
lean_inc(v_a_5143_);
v_a_5144_ = lean_ctor_get(v___x_5142_, 1);
lean_inc(v_a_5144_);
lean_dec_ref_known(v___x_5142_, 2);
v_a_5132_ = v_a_5143_;
v_a_5133_ = v_a_5144_;
goto v___jp_5131_;
}
else
{
lean_dec_ref(v_mkLit_5124_);
lean_dec_ref(v_mkElem_5123_);
lean_dec_ref(v_mkAppend_5122_);
return v___x_5142_;
}
}
else
{
lean_dec(v_b_5128_);
v_a_5132_ = v_elem_5138_;
v_a_5133_ = v___y_5140_;
goto v___jp_5131_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5173_, lean_object* v_mkElem_5174_, lean_object* v_mkLit_5175_, lean_object* v_as_5176_, lean_object* v_sz_5177_, lean_object* v_i_5178_, lean_object* v_b_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_){
_start:
{
size_t v_sz_boxed_5182_; size_t v_i_boxed_5183_; lean_object* v_res_5184_; 
v_sz_boxed_5182_ = lean_unbox_usize(v_sz_5177_);
lean_dec(v_sz_5177_);
v_i_boxed_5183_ = lean_unbox_usize(v_i_5178_);
lean_dec(v_i_5178_);
v_res_5184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5173_, v_mkElem_5174_, v_mkLit_5175_, v_as_5176_, v_sz_boxed_5182_, v_i_boxed_5183_, v_b_5179_, v___y_5180_, v___y_5181_);
lean_dec_ref(v___y_5180_);
lean_dec_ref(v_as_5176_);
return v_res_5184_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5185_, lean_object* v_mkAppend_5186_, lean_object* v_mkElem_5187_, lean_object* v_mkLit_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_){
_start:
{
lean_object* v_result_5191_; size_t v_sz_5192_; size_t v___x_5193_; lean_object* v___x_5194_; 
v_result_5191_ = lean_box(0);
v_sz_5192_ = lean_array_size(v_chunks_5185_);
v___x_5193_ = ((size_t)0ULL);
lean_inc_ref(v_mkLit_5188_);
v___x_5194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5186_, v_mkElem_5187_, v_mkLit_5188_, v_chunks_5185_, v_sz_5192_, v___x_5193_, v_result_5191_, v_a_5189_, v_a_5190_);
if (lean_obj_tag(v___x_5194_) == 0)
{
lean_object* v_a_5195_; lean_object* v_a_5196_; uint8_t v___x_5197_; 
v_a_5195_ = lean_ctor_get(v___x_5194_, 0);
lean_inc(v_a_5195_);
v_a_5196_ = lean_ctor_get(v___x_5194_, 1);
lean_inc(v_a_5196_);
v___x_5197_ = l_Lean_Syntax_isMissing(v_a_5195_);
lean_dec(v_a_5195_);
if (v___x_5197_ == 0)
{
lean_dec(v_a_5196_);
lean_dec_ref(v_mkLit_5188_);
return v___x_5194_;
}
else
{
lean_object* v___x_5198_; lean_object* v___x_5199_; 
lean_dec_ref_known(v___x_5194_, 2);
v___x_5198_ = ((lean_object*)(l_Lean_versionString___closed__0));
lean_inc_ref(v_a_5189_);
v___x_5199_ = lean_apply_3(v_mkLit_5188_, v___x_5198_, v_a_5189_, v_a_5196_);
return v___x_5199_;
}
}
else
{
lean_dec_ref(v_mkLit_5188_);
return v___x_5194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5200_, lean_object* v_mkAppend_5201_, lean_object* v_mkElem_5202_, lean_object* v_mkLit_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_){
_start:
{
lean_object* v_res_5206_; 
v_res_5206_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5200_, v_mkAppend_5201_, v_mkElem_5202_, v_mkLit_5203_, v_a_5204_, v_a_5205_);
lean_dec_ref(v_a_5204_);
lean_dec_ref(v_chunks_5200_);
return v_res_5206_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5211_, lean_object* v_b_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_){
_start:
{
lean_object* v_ref_5215_; uint8_t v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; 
v_ref_5215_ = lean_ctor_get(v___y_5213_, 5);
v___x_5216_ = 0;
v___x_5217_ = l_Lean_SourceInfo_fromRef(v_ref_5215_, v___x_5216_);
v___x_5218_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5219_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5217_);
v___x_5220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5220_, 0, v___x_5217_);
lean_ctor_set(v___x_5220_, 1, v___x_5219_);
v___x_5221_ = l_Lean_Syntax_node3(v___x_5217_, v___x_5218_, v_a_5211_, v___x_5220_, v_b_5212_);
v___x_5222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5221_);
lean_ctor_set(v___x_5222_, 1, v___y_5214_);
return v___x_5222_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5223_, lean_object* v_b_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_){
_start:
{
lean_object* v_res_5227_; 
v_res_5227_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5223_, v_b_5224_, v___y_5225_, v___y_5226_);
lean_dec_ref(v___y_5225_);
return v_res_5227_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5228_, lean_object* v_a_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_){
_start:
{
lean_object* v_ref_5232_; uint8_t v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; 
v_ref_5232_ = lean_ctor_get(v___y_5230_, 5);
v___x_5233_ = 0;
v___x_5234_ = l_Lean_SourceInfo_fromRef(v_ref_5232_, v___x_5233_);
v___x_5235_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5236_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5234_);
v___x_5237_ = l_Lean_Syntax_node1(v___x_5234_, v___x_5236_, v_a_5229_);
v___x_5238_ = l_Lean_Syntax_node2(v___x_5234_, v___x_5235_, v_ofInterpFn_5228_, v___x_5237_);
v___x_5239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5239_, 0, v___x_5238_);
lean_ctor_set(v___x_5239_, 1, v___y_5231_);
return v___x_5239_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5240_, lean_object* v_a_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_){
_start:
{
lean_object* v_res_5244_; 
v_res_5244_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5240_, v_a_5241_, v___y_5242_, v___y_5243_);
lean_dec_ref(v___y_5242_);
return v_res_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5245_, lean_object* v_s_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_){
_start:
{
lean_object* v_ref_5249_; uint8_t v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; 
v_ref_5249_ = lean_ctor_get(v___y_5247_, 5);
v___x_5250_ = 0;
v___x_5251_ = l_Lean_SourceInfo_fromRef(v_ref_5249_, v___x_5250_);
v___x_5252_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5253_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5254_ = lean_box(2);
v___x_5255_ = l_Lean_Syntax_mkStrLit(v_s_5246_, v___x_5254_);
lean_inc(v___x_5251_);
v___x_5256_ = l_Lean_Syntax_node1(v___x_5251_, v___x_5253_, v___x_5255_);
v___x_5257_ = l_Lean_Syntax_node2(v___x_5251_, v___x_5252_, v_ofLitFn_5245_, v___x_5256_);
v___x_5258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5258_, 0, v___x_5257_);
lean_ctor_set(v___x_5258_, 1, v___y_5248_);
return v___x_5258_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5259_, lean_object* v_s_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_){
_start:
{
lean_object* v_res_5263_; 
v_res_5263_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5259_, v_s_5260_, v___y_5261_, v___y_5262_);
lean_dec_ref(v___y_5261_);
return v_res_5263_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5281_; lean_object* v___x_5282_; 
v___x_5281_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5282_ = l_String_toRawSubstring_x27(v___x_5281_);
return v___x_5282_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5303_, lean_object* v_type_5304_, lean_object* v_ofInterpFn_5305_, lean_object* v_ofLitFn_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_){
_start:
{
lean_object* v___f_5309_; lean_object* v___f_5310_; lean_object* v___f_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; 
v___f_5309_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5310_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5310_, 0, v_ofInterpFn_5305_);
v___f_5311_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5311_, 0, v_ofLitFn_5306_);
v___x_5312_ = l_Lean_Syntax_getArgs(v_interpStr_5303_);
v___x_5313_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5312_, v___f_5309_, v___f_5310_, v___f_5311_, v_a_5307_, v_a_5308_);
lean_dec_ref(v___x_5312_);
if (lean_obj_tag(v___x_5313_) == 0)
{
lean_object* v_a_5314_; lean_object* v_a_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5346_; 
v_a_5314_ = lean_ctor_get(v___x_5313_, 0);
v_a_5315_ = lean_ctor_get(v___x_5313_, 1);
v_isSharedCheck_5346_ = !lean_is_exclusive(v___x_5313_);
if (v_isSharedCheck_5346_ == 0)
{
v___x_5317_ = v___x_5313_;
v_isShared_5318_ = v_isSharedCheck_5346_;
goto v_resetjp_5316_;
}
else
{
lean_inc(v_a_5315_);
lean_inc(v_a_5314_);
lean_dec(v___x_5313_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5346_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
lean_object* v_quotContext_5319_; lean_object* v_currMacroScope_5320_; lean_object* v_ref_5321_; uint8_t v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5344_; 
v_quotContext_5319_ = lean_ctor_get(v_a_5307_, 1);
v_currMacroScope_5320_ = lean_ctor_get(v_a_5307_, 2);
v_ref_5321_ = lean_ctor_get(v_a_5307_, 5);
v___x_5322_ = 0;
v___x_5323_ = l_Lean_SourceInfo_fromRef(v_ref_5321_, v___x_5322_);
v___x_5324_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5325_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5326_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc_n(v___x_5323_, 7);
v___x_5327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5327_, 0, v___x_5323_);
lean_ctor_set(v___x_5327_, 1, v___x_5326_);
v___x_5328_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5329_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5330_ = lean_box(0);
lean_inc(v_currMacroScope_5320_);
lean_inc(v_quotContext_5319_);
v___x_5331_ = l_Lean_addMacroScope(v_quotContext_5319_, v___x_5330_, v_currMacroScope_5320_);
v___x_5332_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
v___x_5333_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5333_, 0, v___x_5323_);
lean_ctor_set(v___x_5333_, 1, v___x_5329_);
lean_ctor_set(v___x_5333_, 2, v___x_5331_);
lean_ctor_set(v___x_5333_, 3, v___x_5332_);
v___x_5334_ = l_Lean_Syntax_node1(v___x_5323_, v___x_5328_, v___x_5333_);
v___x_5335_ = l_Lean_Syntax_node2(v___x_5323_, v___x_5325_, v___x_5327_, v___x_5334_);
v___x_5336_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_5337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5337_, 0, v___x_5323_);
lean_ctor_set(v___x_5337_, 1, v___x_5336_);
v___x_5338_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5339_ = l_Lean_Syntax_node1(v___x_5323_, v___x_5338_, v_type_5304_);
v___x_5340_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
v___x_5341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5323_);
lean_ctor_set(v___x_5341_, 1, v___x_5340_);
v___x_5342_ = l_Lean_Syntax_node5(v___x_5323_, v___x_5324_, v___x_5335_, v_a_5314_, v___x_5337_, v___x_5339_, v___x_5341_);
if (v_isShared_5318_ == 0)
{
lean_ctor_set(v___x_5317_, 0, v___x_5342_);
v___x_5344_ = v___x_5317_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v___x_5342_);
lean_ctor_set(v_reuseFailAlloc_5345_, 1, v_a_5315_);
v___x_5344_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
return v___x_5344_;
}
}
}
else
{
lean_object* v_a_5347_; lean_object* v_a_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5355_; 
lean_dec(v_type_5304_);
v_a_5347_ = lean_ctor_get(v___x_5313_, 0);
v_a_5348_ = lean_ctor_get(v___x_5313_, 1);
v_isSharedCheck_5355_ = !lean_is_exclusive(v___x_5313_);
if (v_isSharedCheck_5355_ == 0)
{
v___x_5350_ = v___x_5313_;
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_a_5348_);
lean_inc(v_a_5347_);
lean_dec(v___x_5313_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v___x_5353_; 
if (v_isShared_5351_ == 0)
{
v___x_5353_ = v___x_5350_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v_a_5347_);
lean_ctor_set(v_reuseFailAlloc_5354_, 1, v_a_5348_);
v___x_5353_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
return v___x_5353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5356_, lean_object* v_type_5357_, lean_object* v_ofInterpFn_5358_, lean_object* v_ofLitFn_5359_, lean_object* v_a_5360_, lean_object* v_a_5361_){
_start:
{
lean_object* v_res_5362_; 
v_res_5362_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5356_, v_type_5357_, v_ofInterpFn_5358_, v_ofLitFn_5359_, v_a_5360_, v_a_5361_);
lean_dec_ref(v_a_5360_);
lean_dec(v_interpStr_5356_);
return v_res_5362_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5363_){
_start:
{
lean_object* v___x_5364_; lean_object* v___x_5365_; 
v___x_5364_ = lean_unsigned_to_nat(1u);
v___x_5365_ = l_Lean_Syntax_getArg(v_stx_5363_, v___x_5364_);
if (lean_obj_tag(v___x_5365_) == 1)
{
lean_object* v_kind_5366_; 
v_kind_5366_ = lean_ctor_get(v___x_5365_, 1);
lean_inc(v_kind_5366_);
if (lean_obj_tag(v_kind_5366_) == 1)
{
lean_object* v_pre_5367_; 
v_pre_5367_ = lean_ctor_get(v_kind_5366_, 0);
lean_inc(v_pre_5367_);
if (lean_obj_tag(v_pre_5367_) == 1)
{
lean_object* v_pre_5368_; 
v_pre_5368_ = lean_ctor_get(v_pre_5367_, 0);
lean_inc(v_pre_5368_);
if (lean_obj_tag(v_pre_5368_) == 1)
{
lean_object* v_pre_5369_; 
v_pre_5369_ = lean_ctor_get(v_pre_5368_, 0);
lean_inc(v_pre_5369_);
if (lean_obj_tag(v_pre_5369_) == 1)
{
lean_object* v_pre_5370_; 
v_pre_5370_ = lean_ctor_get(v_pre_5369_, 0);
if (lean_obj_tag(v_pre_5370_) == 0)
{
lean_object* v_args_5371_; lean_object* v_str_5372_; lean_object* v_str_5373_; lean_object* v_str_5374_; lean_object* v_str_5375_; lean_object* v___x_5376_; uint8_t v___x_5377_; 
v_args_5371_ = lean_ctor_get(v___x_5365_, 2);
lean_inc_ref(v_args_5371_);
lean_dec_ref_known(v___x_5365_, 3);
v_str_5372_ = lean_ctor_get(v_kind_5366_, 1);
lean_inc_ref(v_str_5372_);
lean_dec_ref_known(v_kind_5366_, 2);
v_str_5373_ = lean_ctor_get(v_pre_5367_, 1);
lean_inc_ref(v_str_5373_);
lean_dec_ref_known(v_pre_5367_, 2);
v_str_5374_ = lean_ctor_get(v_pre_5368_, 1);
lean_inc_ref(v_str_5374_);
lean_dec_ref_known(v_pre_5368_, 2);
v_str_5375_ = lean_ctor_get(v_pre_5369_, 1);
lean_inc_ref(v_str_5375_);
lean_dec_ref_known(v_pre_5369_, 2);
v___x_5376_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__0));
v___x_5377_ = lean_string_dec_eq(v_str_5375_, v___x_5376_);
lean_dec_ref(v_str_5375_);
if (v___x_5377_ == 0)
{
lean_object* v___x_5378_; 
lean_dec_ref(v_str_5374_);
lean_dec_ref(v_str_5373_);
lean_dec_ref(v_str_5372_);
lean_dec_ref(v_args_5371_);
v___x_5378_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5378_;
}
else
{
lean_object* v___x_5379_; uint8_t v___x_5380_; 
v___x_5379_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__1));
v___x_5380_ = lean_string_dec_eq(v_str_5374_, v___x_5379_);
lean_dec_ref(v_str_5374_);
if (v___x_5380_ == 0)
{
lean_object* v___x_5381_; 
lean_dec_ref(v_str_5373_);
lean_dec_ref(v_str_5372_);
lean_dec_ref(v_args_5371_);
v___x_5381_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5381_;
}
else
{
lean_object* v___x_5382_; uint8_t v___x_5383_; 
v___x_5382_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__0));
v___x_5383_ = lean_string_dec_eq(v_str_5373_, v___x_5382_);
lean_dec_ref(v_str_5373_);
if (v___x_5383_ == 0)
{
lean_object* v___x_5384_; 
lean_dec_ref(v_str_5372_);
lean_dec_ref(v_args_5371_);
v___x_5384_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5384_;
}
else
{
lean_object* v___x_5385_; uint8_t v___x_5386_; 
v___x_5385_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__1));
v___x_5386_ = lean_string_dec_eq(v_str_5372_, v___x_5385_);
lean_dec_ref(v_str_5372_);
if (v___x_5386_ == 0)
{
lean_object* v___x_5387_; 
lean_dec_ref(v_args_5371_);
v___x_5387_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5387_;
}
else
{
lean_object* v___x_5388_; lean_object* v___x_5389_; uint8_t v___x_5390_; 
v___x_5388_ = lean_array_get_size(v_args_5371_);
v___x_5389_ = lean_unsigned_to_nat(2u);
v___x_5390_ = lean_nat_dec_eq(v___x_5388_, v___x_5389_);
if (v___x_5390_ == 0)
{
lean_object* v___x_5391_; 
lean_dec_ref(v_args_5371_);
v___x_5391_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5391_;
}
else
{
lean_object* v___x_5392_; lean_object* v___x_5393_; 
v___x_5392_ = lean_unsigned_to_nat(0u);
v___x_5393_ = lean_array_fget(v_args_5371_, v___x_5392_);
lean_dec_ref(v_args_5371_);
if (lean_obj_tag(v___x_5393_) == 2)
{
lean_object* v_val_5394_; 
v_val_5394_ = lean_ctor_get(v___x_5393_, 1);
lean_inc_ref(v_val_5394_);
lean_dec_ref_known(v___x_5393_, 2);
return v_val_5394_;
}
else
{
lean_object* v___x_5395_; 
lean_dec(v___x_5393_);
v___x_5395_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5395_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5396_; 
lean_dec_ref_known(v_pre_5369_, 2);
lean_dec_ref_known(v_pre_5368_, 2);
lean_dec_ref_known(v_pre_5367_, 2);
lean_dec_ref_known(v_kind_5366_, 2);
lean_dec_ref_known(v___x_5365_, 3);
v___x_5396_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5396_;
}
}
else
{
lean_object* v___x_5397_; 
lean_dec_ref_known(v_pre_5368_, 2);
lean_dec(v_pre_5369_);
lean_dec_ref_known(v_pre_5367_, 2);
lean_dec_ref_known(v_kind_5366_, 2);
lean_dec_ref_known(v___x_5365_, 3);
v___x_5397_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5397_;
}
}
else
{
lean_object* v___x_5398_; 
lean_dec(v_pre_5368_);
lean_dec_ref_known(v_pre_5367_, 2);
lean_dec_ref_known(v_kind_5366_, 2);
lean_dec_ref_known(v___x_5365_, 3);
v___x_5398_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5398_;
}
}
else
{
lean_object* v___x_5399_; 
lean_dec(v_pre_5367_);
lean_dec_ref_known(v_kind_5366_, 2);
lean_dec_ref_known(v___x_5365_, 3);
v___x_5399_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5399_;
}
}
else
{
lean_object* v___x_5400_; 
lean_dec_ref_known(v___x_5365_, 3);
lean_dec(v_kind_5366_);
v___x_5400_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5400_;
}
}
else
{
lean_object* v___x_5401_; 
lean_dec(v___x_5365_);
v___x_5401_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* v_stx_5402_){
_start:
{
lean_object* v_res_5403_; 
v_res_5403_ = l_Lean_TSyntax_getDocString(v_stx_5402_);
lean_dec(v_stx_5402_);
return v_res_5403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5422_, lean_object* v_prec_5423_){
_start:
{
lean_object* v___y_5425_; lean_object* v___y_5432_; lean_object* v___y_5439_; lean_object* v___y_5446_; lean_object* v___y_5453_; lean_object* v___y_5460_; 
switch(v_x_5422_)
{
case 0:
{
lean_object* v___x_5466_; uint8_t v___x_5467_; 
v___x_5466_ = lean_unsigned_to_nat(1024u);
v___x_5467_ = lean_nat_dec_le(v___x_5466_, v_prec_5423_);
if (v___x_5467_ == 0)
{
lean_object* v___x_5468_; 
v___x_5468_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5425_ = v___x_5468_;
goto v___jp_5424_;
}
else
{
lean_object* v___x_5469_; 
v___x_5469_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5425_ = v___x_5469_;
goto v___jp_5424_;
}
}
case 1:
{
lean_object* v___x_5470_; uint8_t v___x_5471_; 
v___x_5470_ = lean_unsigned_to_nat(1024u);
v___x_5471_ = lean_nat_dec_le(v___x_5470_, v_prec_5423_);
if (v___x_5471_ == 0)
{
lean_object* v___x_5472_; 
v___x_5472_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5432_ = v___x_5472_;
goto v___jp_5431_;
}
else
{
lean_object* v___x_5473_; 
v___x_5473_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5432_ = v___x_5473_;
goto v___jp_5431_;
}
}
case 2:
{
lean_object* v___x_5474_; uint8_t v___x_5475_; 
v___x_5474_ = lean_unsigned_to_nat(1024u);
v___x_5475_ = lean_nat_dec_le(v___x_5474_, v_prec_5423_);
if (v___x_5475_ == 0)
{
lean_object* v___x_5476_; 
v___x_5476_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5439_ = v___x_5476_;
goto v___jp_5438_;
}
else
{
lean_object* v___x_5477_; 
v___x_5477_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5439_ = v___x_5477_;
goto v___jp_5438_;
}
}
case 3:
{
lean_object* v___x_5478_; uint8_t v___x_5479_; 
v___x_5478_ = lean_unsigned_to_nat(1024u);
v___x_5479_ = lean_nat_dec_le(v___x_5478_, v_prec_5423_);
if (v___x_5479_ == 0)
{
lean_object* v___x_5480_; 
v___x_5480_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5446_ = v___x_5480_;
goto v___jp_5445_;
}
else
{
lean_object* v___x_5481_; 
v___x_5481_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5446_ = v___x_5481_;
goto v___jp_5445_;
}
}
case 4:
{
lean_object* v___x_5482_; uint8_t v___x_5483_; 
v___x_5482_ = lean_unsigned_to_nat(1024u);
v___x_5483_ = lean_nat_dec_le(v___x_5482_, v_prec_5423_);
if (v___x_5483_ == 0)
{
lean_object* v___x_5484_; 
v___x_5484_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5453_ = v___x_5484_;
goto v___jp_5452_;
}
else
{
lean_object* v___x_5485_; 
v___x_5485_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5453_ = v___x_5485_;
goto v___jp_5452_;
}
}
default: 
{
lean_object* v___x_5486_; uint8_t v___x_5487_; 
v___x_5486_ = lean_unsigned_to_nat(1024u);
v___x_5487_ = lean_nat_dec_le(v___x_5486_, v_prec_5423_);
if (v___x_5487_ == 0)
{
lean_object* v___x_5488_; 
v___x_5488_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5460_ = v___x_5488_;
goto v___jp_5459_;
}
else
{
lean_object* v___x_5489_; 
v___x_5489_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5460_ = v___x_5489_;
goto v___jp_5459_;
}
}
}
v___jp_5424_:
{
lean_object* v___x_5426_; lean_object* v___x_5427_; uint8_t v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; 
v___x_5426_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
lean_inc(v___y_5425_);
v___x_5427_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5427_, 0, v___y_5425_);
lean_ctor_set(v___x_5427_, 1, v___x_5426_);
v___x_5428_ = 0;
v___x_5429_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5429_, 0, v___x_5427_);
lean_ctor_set_uint8(v___x_5429_, sizeof(void*)*1, v___x_5428_);
v___x_5430_ = l_Repr_addAppParen(v___x_5429_, v_prec_5423_);
return v___x_5430_;
}
v___jp_5431_:
{
lean_object* v___x_5433_; lean_object* v___x_5434_; uint8_t v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; 
v___x_5433_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__3));
lean_inc(v___y_5432_);
v___x_5434_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5434_, 0, v___y_5432_);
lean_ctor_set(v___x_5434_, 1, v___x_5433_);
v___x_5435_ = 0;
v___x_5436_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5436_, 0, v___x_5434_);
lean_ctor_set_uint8(v___x_5436_, sizeof(void*)*1, v___x_5435_);
v___x_5437_ = l_Repr_addAppParen(v___x_5436_, v_prec_5423_);
return v___x_5437_;
}
v___jp_5438_:
{
lean_object* v___x_5440_; lean_object* v___x_5441_; uint8_t v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; 
v___x_5440_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__5));
lean_inc(v___y_5439_);
v___x_5441_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5441_, 0, v___y_5439_);
lean_ctor_set(v___x_5441_, 1, v___x_5440_);
v___x_5442_ = 0;
v___x_5443_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5443_, 0, v___x_5441_);
lean_ctor_set_uint8(v___x_5443_, sizeof(void*)*1, v___x_5442_);
v___x_5444_ = l_Repr_addAppParen(v___x_5443_, v_prec_5423_);
return v___x_5444_;
}
v___jp_5445_:
{
lean_object* v___x_5447_; lean_object* v___x_5448_; uint8_t v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; 
v___x_5447_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__7));
lean_inc(v___y_5446_);
v___x_5448_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5448_, 0, v___y_5446_);
lean_ctor_set(v___x_5448_, 1, v___x_5447_);
v___x_5449_ = 0;
v___x_5450_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5450_, 0, v___x_5448_);
lean_ctor_set_uint8(v___x_5450_, sizeof(void*)*1, v___x_5449_);
v___x_5451_ = l_Repr_addAppParen(v___x_5450_, v_prec_5423_);
return v___x_5451_;
}
v___jp_5452_:
{
lean_object* v___x_5454_; lean_object* v___x_5455_; uint8_t v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; 
v___x_5454_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__9));
lean_inc(v___y_5453_);
v___x_5455_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5455_, 0, v___y_5453_);
lean_ctor_set(v___x_5455_, 1, v___x_5454_);
v___x_5456_ = 0;
v___x_5457_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5457_, 0, v___x_5455_);
lean_ctor_set_uint8(v___x_5457_, sizeof(void*)*1, v___x_5456_);
v___x_5458_ = l_Repr_addAppParen(v___x_5457_, v_prec_5423_);
return v___x_5458_;
}
v___jp_5459_:
{
lean_object* v___x_5461_; lean_object* v___x_5462_; uint8_t v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; 
v___x_5461_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__11));
lean_inc(v___y_5460_);
v___x_5462_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5462_, 0, v___y_5460_);
lean_ctor_set(v___x_5462_, 1, v___x_5461_);
v___x_5463_ = 0;
v___x_5464_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5464_, 0, v___x_5462_);
lean_ctor_set_uint8(v___x_5464_, sizeof(void*)*1, v___x_5463_);
v___x_5465_ = l_Repr_addAppParen(v___x_5464_, v_prec_5423_);
return v___x_5465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5490_, lean_object* v_prec_5491_){
_start:
{
uint8_t v_x_329__boxed_5492_; lean_object* v_res_5493_; 
v_x_329__boxed_5492_ = lean_unbox(v_x_5490_);
v_res_5493_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_329__boxed_5492_, v_prec_5491_);
lean_dec(v_prec_5491_);
return v_res_5493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5505_, lean_object* v_prec_5506_){
_start:
{
lean_object* v___y_5508_; lean_object* v___y_5515_; lean_object* v___y_5522_; 
switch(v_x_5505_)
{
case 0:
{
lean_object* v___x_5528_; uint8_t v___x_5529_; 
v___x_5528_ = lean_unsigned_to_nat(1024u);
v___x_5529_ = lean_nat_dec_le(v___x_5528_, v_prec_5506_);
if (v___x_5529_ == 0)
{
lean_object* v___x_5530_; 
v___x_5530_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5508_ = v___x_5530_;
goto v___jp_5507_;
}
else
{
lean_object* v___x_5531_; 
v___x_5531_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5508_ = v___x_5531_;
goto v___jp_5507_;
}
}
case 1:
{
lean_object* v___x_5532_; uint8_t v___x_5533_; 
v___x_5532_ = lean_unsigned_to_nat(1024u);
v___x_5533_ = lean_nat_dec_le(v___x_5532_, v_prec_5506_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5534_; 
v___x_5534_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5515_ = v___x_5534_;
goto v___jp_5514_;
}
else
{
lean_object* v___x_5535_; 
v___x_5535_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5515_ = v___x_5535_;
goto v___jp_5514_;
}
}
default: 
{
lean_object* v___x_5536_; uint8_t v___x_5537_; 
v___x_5536_ = lean_unsigned_to_nat(1024u);
v___x_5537_ = lean_nat_dec_le(v___x_5536_, v_prec_5506_);
if (v___x_5537_ == 0)
{
lean_object* v___x_5538_; 
v___x_5538_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5522_ = v___x_5538_;
goto v___jp_5521_;
}
else
{
lean_object* v___x_5539_; 
v___x_5539_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5522_ = v___x_5539_;
goto v___jp_5521_;
}
}
}
v___jp_5507_:
{
lean_object* v___x_5509_; lean_object* v___x_5510_; uint8_t v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; 
v___x_5509_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
lean_inc(v___y_5508_);
v___x_5510_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5510_, 0, v___y_5508_);
lean_ctor_set(v___x_5510_, 1, v___x_5509_);
v___x_5511_ = 0;
v___x_5512_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5512_, 0, v___x_5510_);
lean_ctor_set_uint8(v___x_5512_, sizeof(void*)*1, v___x_5511_);
v___x_5513_ = l_Repr_addAppParen(v___x_5512_, v_prec_5506_);
return v___x_5513_;
}
v___jp_5514_:
{
lean_object* v___x_5516_; lean_object* v___x_5517_; uint8_t v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; 
v___x_5516_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
lean_inc(v___y_5515_);
v___x_5517_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5517_, 0, v___y_5515_);
lean_ctor_set(v___x_5517_, 1, v___x_5516_);
v___x_5518_ = 0;
v___x_5519_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5519_, 0, v___x_5517_);
lean_ctor_set_uint8(v___x_5519_, sizeof(void*)*1, v___x_5518_);
v___x_5520_ = l_Repr_addAppParen(v___x_5519_, v_prec_5506_);
return v___x_5520_;
}
v___jp_5521_:
{
lean_object* v___x_5523_; lean_object* v___x_5524_; uint8_t v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; 
v___x_5523_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
lean_inc(v___y_5522_);
v___x_5524_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5524_, 0, v___y_5522_);
lean_ctor_set(v___x_5524_, 1, v___x_5523_);
v___x_5525_ = 0;
v___x_5526_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5526_, 0, v___x_5524_);
lean_ctor_set_uint8(v___x_5526_, sizeof(void*)*1, v___x_5525_);
v___x_5527_ = l_Repr_addAppParen(v___x_5526_, v_prec_5506_);
return v___x_5527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5540_, lean_object* v_prec_5541_){
_start:
{
uint8_t v_x_167__boxed_5542_; lean_object* v_res_5543_; 
v_x_167__boxed_5542_ = lean_unbox(v_x_5540_);
v_res_5543_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_167__boxed_5542_, v_prec_5541_);
lean_dec(v_prec_5541_);
return v_res_5543_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5555_; lean_object* v___x_5556_; 
v___x_5555_ = lean_unsigned_to_nat(8u);
v___x_5556_ = lean_nat_to_int(v___x_5555_);
return v___x_5556_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5566_; lean_object* v___x_5567_; 
v___x_5566_ = lean_unsigned_to_nat(13u);
v___x_5567_ = lean_nat_to_int(v___x_5566_);
return v___x_5567_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5577_; lean_object* v___x_5578_; 
v___x_5577_ = lean_unsigned_to_nat(10u);
v___x_5578_ = lean_nat_to_int(v___x_5577_);
return v___x_5578_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5582_; lean_object* v___x_5583_; 
v___x_5582_ = lean_unsigned_to_nat(14u);
v___x_5583_ = lean_nat_to_int(v___x_5582_);
return v___x_5583_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5587_; lean_object* v___x_5588_; 
v___x_5587_ = lean_unsigned_to_nat(19u);
v___x_5588_ = lean_nat_to_int(v___x_5587_);
return v___x_5588_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5592_; lean_object* v___x_5593_; 
v___x_5592_ = lean_unsigned_to_nat(20u);
v___x_5593_ = lean_nat_to_int(v___x_5592_);
return v___x_5593_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5600_; lean_object* v___x_5601_; 
v___x_5600_ = lean_unsigned_to_nat(9u);
v___x_5601_ = lean_nat_to_int(v___x_5600_);
return v___x_5601_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5608_; lean_object* v___x_5609_; 
v___x_5608_ = lean_unsigned_to_nat(12u);
v___x_5609_ = lean_nat_to_int(v___x_5608_);
return v___x_5609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5616_){
_start:
{
uint8_t v_zeta_5617_; uint8_t v_beta_5618_; uint8_t v_eta_5619_; uint8_t v_etaStruct_5620_; uint8_t v_iota_5621_; uint8_t v_proj_5622_; uint8_t v_decide_5623_; uint8_t v_autoUnfold_5624_; uint8_t v_failIfUnchanged_5625_; uint8_t v_unfoldPartialApp_5626_; uint8_t v_zetaDelta_5627_; uint8_t v_index_5628_; uint8_t v_zetaUnused_5629_; uint8_t v_zetaHave_5630_; uint8_t v_locals_5631_; uint8_t v_instances_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; uint8_t v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; 
v_zeta_5617_ = lean_ctor_get_uint8(v_x_5616_, 0);
v_beta_5618_ = lean_ctor_get_uint8(v_x_5616_, 1);
v_eta_5619_ = lean_ctor_get_uint8(v_x_5616_, 2);
v_etaStruct_5620_ = lean_ctor_get_uint8(v_x_5616_, 3);
v_iota_5621_ = lean_ctor_get_uint8(v_x_5616_, 4);
v_proj_5622_ = lean_ctor_get_uint8(v_x_5616_, 5);
v_decide_5623_ = lean_ctor_get_uint8(v_x_5616_, 6);
v_autoUnfold_5624_ = lean_ctor_get_uint8(v_x_5616_, 7);
v_failIfUnchanged_5625_ = lean_ctor_get_uint8(v_x_5616_, 8);
v_unfoldPartialApp_5626_ = lean_ctor_get_uint8(v_x_5616_, 9);
v_zetaDelta_5627_ = lean_ctor_get_uint8(v_x_5616_, 10);
v_index_5628_ = lean_ctor_get_uint8(v_x_5616_, 11);
v_zetaUnused_5629_ = lean_ctor_get_uint8(v_x_5616_, 12);
v_zetaHave_5630_ = lean_ctor_get_uint8(v_x_5616_, 13);
v_locals_5631_ = lean_ctor_get_uint8(v_x_5616_, 14);
v_instances_5632_ = lean_ctor_get_uint8(v_x_5616_, 15);
v___x_5633_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5634_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5635_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5636_ = lean_unsigned_to_nat(0u);
v___x_5637_ = l_Bool_repr___redArg(v_zeta_5617_);
v___x_5638_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5638_, 0, v___x_5635_);
lean_ctor_set(v___x_5638_, 1, v___x_5637_);
v___x_5639_ = 0;
v___x_5640_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5640_, 0, v___x_5638_);
lean_ctor_set_uint8(v___x_5640_, sizeof(void*)*1, v___x_5639_);
v___x_5641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5634_);
lean_ctor_set(v___x_5641_, 1, v___x_5640_);
v___x_5642_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5641_);
lean_ctor_set(v___x_5643_, 1, v___x_5642_);
v___x_5644_ = lean_box(1);
v___x_5645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5643_);
lean_ctor_set(v___x_5645_, 1, v___x_5644_);
v___x_5646_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5647_, 0, v___x_5645_);
lean_ctor_set(v___x_5647_, 1, v___x_5646_);
v___x_5648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5648_, 0, v___x_5647_);
lean_ctor_set(v___x_5648_, 1, v___x_5633_);
v___x_5649_ = l_Bool_repr___redArg(v_beta_5618_);
v___x_5650_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5650_, 0, v___x_5635_);
lean_ctor_set(v___x_5650_, 1, v___x_5649_);
v___x_5651_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5651_, 0, v___x_5650_);
lean_ctor_set_uint8(v___x_5651_, sizeof(void*)*1, v___x_5639_);
v___x_5652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5652_, 0, v___x_5648_);
lean_ctor_set(v___x_5652_, 1, v___x_5651_);
v___x_5653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5653_, 0, v___x_5652_);
lean_ctor_set(v___x_5653_, 1, v___x_5642_);
v___x_5654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5654_, 0, v___x_5653_);
lean_ctor_set(v___x_5654_, 1, v___x_5644_);
v___x_5655_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5656_, 0, v___x_5654_);
lean_ctor_set(v___x_5656_, 1, v___x_5655_);
v___x_5657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5657_, 0, v___x_5656_);
lean_ctor_set(v___x_5657_, 1, v___x_5633_);
v___x_5658_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5659_ = l_Bool_repr___redArg(v_eta_5619_);
v___x_5660_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5660_, 0, v___x_5658_);
lean_ctor_set(v___x_5660_, 1, v___x_5659_);
v___x_5661_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5661_, 0, v___x_5660_);
lean_ctor_set_uint8(v___x_5661_, sizeof(void*)*1, v___x_5639_);
v___x_5662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5662_, 0, v___x_5657_);
lean_ctor_set(v___x_5662_, 1, v___x_5661_);
v___x_5663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5662_);
lean_ctor_set(v___x_5663_, 1, v___x_5642_);
v___x_5664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5663_);
lean_ctor_set(v___x_5664_, 1, v___x_5644_);
v___x_5665_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5666_, 0, v___x_5664_);
lean_ctor_set(v___x_5666_, 1, v___x_5665_);
v___x_5667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5667_, 0, v___x_5666_);
lean_ctor_set(v___x_5667_, 1, v___x_5633_);
v___x_5668_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5669_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5620_, v___x_5636_);
v___x_5670_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5670_, 0, v___x_5668_);
lean_ctor_set(v___x_5670_, 1, v___x_5669_);
v___x_5671_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5671_, 0, v___x_5670_);
lean_ctor_set_uint8(v___x_5671_, sizeof(void*)*1, v___x_5639_);
v___x_5672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5672_, 0, v___x_5667_);
lean_ctor_set(v___x_5672_, 1, v___x_5671_);
v___x_5673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5673_, 0, v___x_5672_);
lean_ctor_set(v___x_5673_, 1, v___x_5642_);
v___x_5674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5674_, 0, v___x_5673_);
lean_ctor_set(v___x_5674_, 1, v___x_5644_);
v___x_5675_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5676_, 0, v___x_5674_);
lean_ctor_set(v___x_5676_, 1, v___x_5675_);
v___x_5677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5677_, 0, v___x_5676_);
lean_ctor_set(v___x_5677_, 1, v___x_5633_);
v___x_5678_ = l_Bool_repr___redArg(v_iota_5621_);
v___x_5679_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5679_, 0, v___x_5635_);
lean_ctor_set(v___x_5679_, 1, v___x_5678_);
v___x_5680_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5680_, 0, v___x_5679_);
lean_ctor_set_uint8(v___x_5680_, sizeof(void*)*1, v___x_5639_);
v___x_5681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5681_, 0, v___x_5677_);
lean_ctor_set(v___x_5681_, 1, v___x_5680_);
v___x_5682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5682_, 0, v___x_5681_);
lean_ctor_set(v___x_5682_, 1, v___x_5642_);
v___x_5683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5683_, 0, v___x_5682_);
lean_ctor_set(v___x_5683_, 1, v___x_5644_);
v___x_5684_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5685_, 0, v___x_5683_);
lean_ctor_set(v___x_5685_, 1, v___x_5684_);
v___x_5686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5685_);
lean_ctor_set(v___x_5686_, 1, v___x_5633_);
v___x_5687_ = l_Bool_repr___redArg(v_proj_5622_);
v___x_5688_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5635_);
lean_ctor_set(v___x_5688_, 1, v___x_5687_);
v___x_5689_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5689_, 0, v___x_5688_);
lean_ctor_set_uint8(v___x_5689_, sizeof(void*)*1, v___x_5639_);
v___x_5690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5690_, 0, v___x_5686_);
lean_ctor_set(v___x_5690_, 1, v___x_5689_);
v___x_5691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5690_);
lean_ctor_set(v___x_5691_, 1, v___x_5642_);
v___x_5692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5692_, 0, v___x_5691_);
lean_ctor_set(v___x_5692_, 1, v___x_5644_);
v___x_5693_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5692_);
lean_ctor_set(v___x_5694_, 1, v___x_5693_);
v___x_5695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5695_, 0, v___x_5694_);
lean_ctor_set(v___x_5695_, 1, v___x_5633_);
v___x_5696_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5697_ = l_Bool_repr___redArg(v_decide_5623_);
v___x_5698_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5696_);
lean_ctor_set(v___x_5698_, 1, v___x_5697_);
v___x_5699_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5699_, 0, v___x_5698_);
lean_ctor_set_uint8(v___x_5699_, sizeof(void*)*1, v___x_5639_);
v___x_5700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5695_);
lean_ctor_set(v___x_5700_, 1, v___x_5699_);
v___x_5701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5701_, 0, v___x_5700_);
lean_ctor_set(v___x_5701_, 1, v___x_5642_);
v___x_5702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5702_, 0, v___x_5701_);
lean_ctor_set(v___x_5702_, 1, v___x_5644_);
v___x_5703_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5704_, 0, v___x_5702_);
lean_ctor_set(v___x_5704_, 1, v___x_5703_);
v___x_5705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5705_, 0, v___x_5704_);
lean_ctor_set(v___x_5705_, 1, v___x_5633_);
v___x_5706_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5707_ = l_Bool_repr___redArg(v_autoUnfold_5624_);
v___x_5708_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5708_, 0, v___x_5706_);
lean_ctor_set(v___x_5708_, 1, v___x_5707_);
v___x_5709_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5709_, 0, v___x_5708_);
lean_ctor_set_uint8(v___x_5709_, sizeof(void*)*1, v___x_5639_);
v___x_5710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5710_, 0, v___x_5705_);
lean_ctor_set(v___x_5710_, 1, v___x_5709_);
v___x_5711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5711_, 0, v___x_5710_);
lean_ctor_set(v___x_5711_, 1, v___x_5642_);
v___x_5712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5712_, 0, v___x_5711_);
lean_ctor_set(v___x_5712_, 1, v___x_5644_);
v___x_5713_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5712_);
lean_ctor_set(v___x_5714_, 1, v___x_5713_);
v___x_5715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5714_);
lean_ctor_set(v___x_5715_, 1, v___x_5633_);
v___x_5716_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5717_ = l_Bool_repr___redArg(v_failIfUnchanged_5625_);
v___x_5718_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5718_, 0, v___x_5716_);
lean_ctor_set(v___x_5718_, 1, v___x_5717_);
v___x_5719_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5719_, 0, v___x_5718_);
lean_ctor_set_uint8(v___x_5719_, sizeof(void*)*1, v___x_5639_);
v___x_5720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5720_, 0, v___x_5715_);
lean_ctor_set(v___x_5720_, 1, v___x_5719_);
v___x_5721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5721_, 0, v___x_5720_);
lean_ctor_set(v___x_5721_, 1, v___x_5642_);
v___x_5722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5722_, 0, v___x_5721_);
lean_ctor_set(v___x_5722_, 1, v___x_5644_);
v___x_5723_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5724_, 0, v___x_5722_);
lean_ctor_set(v___x_5724_, 1, v___x_5723_);
v___x_5725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5725_, 0, v___x_5724_);
lean_ctor_set(v___x_5725_, 1, v___x_5633_);
v___x_5726_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5727_ = l_Bool_repr___redArg(v_unfoldPartialApp_5626_);
v___x_5728_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5726_);
lean_ctor_set(v___x_5728_, 1, v___x_5727_);
v___x_5729_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5729_, 0, v___x_5728_);
lean_ctor_set_uint8(v___x_5729_, sizeof(void*)*1, v___x_5639_);
v___x_5730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5725_);
lean_ctor_set(v___x_5730_, 1, v___x_5729_);
v___x_5731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5731_, 0, v___x_5730_);
lean_ctor_set(v___x_5731_, 1, v___x_5642_);
v___x_5732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5731_);
lean_ctor_set(v___x_5732_, 1, v___x_5644_);
v___x_5733_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5734_, 0, v___x_5732_);
lean_ctor_set(v___x_5734_, 1, v___x_5733_);
v___x_5735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5735_, 0, v___x_5734_);
lean_ctor_set(v___x_5735_, 1, v___x_5633_);
v___x_5736_ = l_Bool_repr___redArg(v_zetaDelta_5627_);
v___x_5737_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5737_, 0, v___x_5668_);
lean_ctor_set(v___x_5737_, 1, v___x_5736_);
v___x_5738_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5738_, 0, v___x_5737_);
lean_ctor_set_uint8(v___x_5738_, sizeof(void*)*1, v___x_5639_);
v___x_5739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5739_, 0, v___x_5735_);
lean_ctor_set(v___x_5739_, 1, v___x_5738_);
v___x_5740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5740_, 0, v___x_5739_);
lean_ctor_set(v___x_5740_, 1, v___x_5642_);
v___x_5741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5741_, 0, v___x_5740_);
lean_ctor_set(v___x_5741_, 1, v___x_5644_);
v___x_5742_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5741_);
lean_ctor_set(v___x_5743_, 1, v___x_5742_);
v___x_5744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5744_, 0, v___x_5743_);
lean_ctor_set(v___x_5744_, 1, v___x_5633_);
v___x_5745_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5746_ = l_Bool_repr___redArg(v_index_5628_);
v___x_5747_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5747_, 0, v___x_5745_);
lean_ctor_set(v___x_5747_, 1, v___x_5746_);
v___x_5748_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5748_, 0, v___x_5747_);
lean_ctor_set_uint8(v___x_5748_, sizeof(void*)*1, v___x_5639_);
v___x_5749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5749_, 0, v___x_5744_);
lean_ctor_set(v___x_5749_, 1, v___x_5748_);
v___x_5750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5750_, 0, v___x_5749_);
lean_ctor_set(v___x_5750_, 1, v___x_5642_);
v___x_5751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5750_);
lean_ctor_set(v___x_5751_, 1, v___x_5644_);
v___x_5752_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5753_, 0, v___x_5751_);
lean_ctor_set(v___x_5753_, 1, v___x_5752_);
v___x_5754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5754_, 0, v___x_5753_);
lean_ctor_set(v___x_5754_, 1, v___x_5633_);
v___x_5755_ = l_Bool_repr___redArg(v_zetaUnused_5629_);
v___x_5756_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5706_);
lean_ctor_set(v___x_5756_, 1, v___x_5755_);
v___x_5757_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5757_, 0, v___x_5756_);
lean_ctor_set_uint8(v___x_5757_, sizeof(void*)*1, v___x_5639_);
v___x_5758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5758_, 0, v___x_5754_);
lean_ctor_set(v___x_5758_, 1, v___x_5757_);
v___x_5759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5759_, 0, v___x_5758_);
lean_ctor_set(v___x_5759_, 1, v___x_5642_);
v___x_5760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5760_, 0, v___x_5759_);
lean_ctor_set(v___x_5760_, 1, v___x_5644_);
v___x_5761_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5762_, 0, v___x_5760_);
lean_ctor_set(v___x_5762_, 1, v___x_5761_);
v___x_5763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5763_, 0, v___x_5762_);
lean_ctor_set(v___x_5763_, 1, v___x_5633_);
v___x_5764_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5765_ = l_Bool_repr___redArg(v_zetaHave_5630_);
v___x_5766_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5766_, 0, v___x_5764_);
lean_ctor_set(v___x_5766_, 1, v___x_5765_);
v___x_5767_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5767_, 0, v___x_5766_);
lean_ctor_set_uint8(v___x_5767_, sizeof(void*)*1, v___x_5639_);
v___x_5768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5768_, 0, v___x_5763_);
lean_ctor_set(v___x_5768_, 1, v___x_5767_);
v___x_5769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5769_, 0, v___x_5768_);
lean_ctor_set(v___x_5769_, 1, v___x_5642_);
v___x_5770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5770_, 0, v___x_5769_);
lean_ctor_set(v___x_5770_, 1, v___x_5644_);
v___x_5771_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5772_, 0, v___x_5770_);
lean_ctor_set(v___x_5772_, 1, v___x_5771_);
v___x_5773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5773_, 0, v___x_5772_);
lean_ctor_set(v___x_5773_, 1, v___x_5633_);
v___x_5774_ = l_Bool_repr___redArg(v_locals_5631_);
v___x_5775_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5775_, 0, v___x_5696_);
lean_ctor_set(v___x_5775_, 1, v___x_5774_);
v___x_5776_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5776_, 0, v___x_5775_);
lean_ctor_set_uint8(v___x_5776_, sizeof(void*)*1, v___x_5639_);
v___x_5777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5777_, 0, v___x_5773_);
lean_ctor_set(v___x_5777_, 1, v___x_5776_);
v___x_5778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5778_, 0, v___x_5777_);
lean_ctor_set(v___x_5778_, 1, v___x_5642_);
v___x_5779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5779_, 0, v___x_5778_);
lean_ctor_set(v___x_5779_, 1, v___x_5644_);
v___x_5780_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5781_, 0, v___x_5779_);
lean_ctor_set(v___x_5781_, 1, v___x_5780_);
v___x_5782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5782_, 0, v___x_5781_);
lean_ctor_set(v___x_5782_, 1, v___x_5633_);
v___x_5783_ = l_Bool_repr___redArg(v_instances_5632_);
v___x_5784_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5784_, 0, v___x_5668_);
lean_ctor_set(v___x_5784_, 1, v___x_5783_);
v___x_5785_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5785_, 0, v___x_5784_);
lean_ctor_set_uint8(v___x_5785_, sizeof(void*)*1, v___x_5639_);
v___x_5786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5786_, 0, v___x_5782_);
lean_ctor_set(v___x_5786_, 1, v___x_5785_);
v___x_5787_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5788_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5789_, 0, v___x_5788_);
lean_ctor_set(v___x_5789_, 1, v___x_5786_);
v___x_5790_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5791_, 0, v___x_5789_);
lean_ctor_set(v___x_5791_, 1, v___x_5790_);
v___x_5792_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5792_, 0, v___x_5787_);
lean_ctor_set(v___x_5792_, 1, v___x_5791_);
v___x_5793_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5793_, 0, v___x_5792_);
lean_ctor_set_uint8(v___x_5793_, sizeof(void*)*1, v___x_5639_);
return v___x_5793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5794_){
_start:
{
lean_object* v_res_5795_; 
v_res_5795_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5794_);
lean_dec_ref(v_x_5794_);
return v_res_5795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5796_, lean_object* v_prec_5797_){
_start:
{
lean_object* v___x_5798_; 
v___x_5798_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5796_);
return v___x_5798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5799_, lean_object* v_prec_5800_){
_start:
{
lean_object* v_res_5801_; 
v_res_5801_ = l_Lean_Meta_instReprConfig_repr(v_x_5799_, v_prec_5800_);
lean_dec(v_prec_5800_);
lean_dec_ref(v_x_5799_);
return v_res_5801_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5809_, lean_object* v_x_5810_){
_start:
{
if (lean_obj_tag(v_x_5809_) == 0)
{
lean_object* v___x_5811_; 
v___x_5811_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5811_;
}
else
{
lean_object* v_val_5812_; lean_object* v___x_5814_; uint8_t v_isShared_5815_; uint8_t v_isSharedCheck_5823_; 
v_val_5812_ = lean_ctor_get(v_x_5809_, 0);
v_isSharedCheck_5823_ = !lean_is_exclusive(v_x_5809_);
if (v_isSharedCheck_5823_ == 0)
{
v___x_5814_ = v_x_5809_;
v_isShared_5815_ = v_isSharedCheck_5823_;
goto v_resetjp_5813_;
}
else
{
lean_inc(v_val_5812_);
lean_dec(v_x_5809_);
v___x_5814_ = lean_box(0);
v_isShared_5815_ = v_isSharedCheck_5823_;
goto v_resetjp_5813_;
}
v_resetjp_5813_:
{
lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5819_; 
v___x_5816_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5817_ = l_Nat_reprFast(v_val_5812_);
if (v_isShared_5815_ == 0)
{
lean_ctor_set_tag(v___x_5814_, 3);
lean_ctor_set(v___x_5814_, 0, v___x_5817_);
v___x_5819_ = v___x_5814_;
goto v_reusejp_5818_;
}
else
{
lean_object* v_reuseFailAlloc_5822_; 
v_reuseFailAlloc_5822_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5822_, 0, v___x_5817_);
v___x_5819_ = v_reuseFailAlloc_5822_;
goto v_reusejp_5818_;
}
v_reusejp_5818_:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; 
v___x_5820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5820_, 0, v___x_5816_);
lean_ctor_set(v___x_5820_, 1, v___x_5819_);
v___x_5821_ = l_Repr_addAppParen(v___x_5820_, v_x_5810_);
return v___x_5821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5824_, lean_object* v_x_5825_){
_start:
{
lean_object* v_res_5826_; 
v_res_5826_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5824_, v_x_5825_);
lean_dec(v_x_5825_);
return v_res_5826_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5839_; lean_object* v___x_5840_; 
v___x_5839_ = lean_unsigned_to_nat(21u);
v___x_5840_ = lean_nat_to_int(v___x_5839_);
return v___x_5840_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5847_; lean_object* v___x_5848_; 
v___x_5847_ = lean_unsigned_to_nat(11u);
v___x_5848_ = lean_nat_to_int(v___x_5847_);
return v___x_5848_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5864_; lean_object* v___x_5865_; 
v___x_5864_ = lean_unsigned_to_nat(23u);
v___x_5865_ = lean_nat_to_int(v___x_5864_);
return v___x_5865_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5869_; lean_object* v___x_5870_; 
v___x_5869_ = lean_unsigned_to_nat(16u);
v___x_5870_ = lean_nat_to_int(v___x_5869_);
return v___x_5870_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5877_; lean_object* v___x_5878_; 
v___x_5877_ = lean_unsigned_to_nat(15u);
v___x_5878_ = lean_nat_to_int(v___x_5877_);
return v___x_5878_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5885_; lean_object* v___x_5886_; 
v___x_5885_ = lean_unsigned_to_nat(17u);
v___x_5886_ = lean_nat_to_int(v___x_5885_);
return v___x_5886_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5893_; lean_object* v___x_5894_; 
v___x_5893_ = lean_unsigned_to_nat(18u);
v___x_5894_ = lean_nat_to_int(v___x_5893_);
return v___x_5894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5895_){
_start:
{
lean_object* v_maxSteps_5896_; lean_object* v_maxDischargeDepth_5897_; uint8_t v_contextual_5898_; uint8_t v_memoize_5899_; uint8_t v_singlePass_5900_; uint8_t v_zeta_5901_; uint8_t v_beta_5902_; uint8_t v_eta_5903_; uint8_t v_etaStruct_5904_; uint8_t v_iota_5905_; uint8_t v_proj_5906_; uint8_t v_decide_5907_; uint8_t v_arith_5908_; uint8_t v_autoUnfold_5909_; uint8_t v_dsimp_5910_; uint8_t v_failIfUnchanged_5911_; uint8_t v_ground_5912_; uint8_t v_unfoldPartialApp_5913_; uint8_t v_zetaDelta_5914_; uint8_t v_index_5915_; uint8_t v_implicitDefEqProofs_5916_; uint8_t v_zetaUnused_5917_; uint8_t v_catchRuntime_5918_; uint8_t v_zetaHave_5919_; uint8_t v_letToHave_5920_; uint8_t v_congrConsts_5921_; uint8_t v_bitVecOfNat_5922_; uint8_t v_warnExponents_5923_; uint8_t v_suggestions_5924_; lean_object* v_maxSuggestions_5925_; uint8_t v_locals_5926_; uint8_t v_instances_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; uint8_t v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; lean_object* v___x_6235_; lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; lean_object* v___x_6239_; lean_object* v___x_6240_; lean_object* v___x_6241_; 
v_maxSteps_5896_ = lean_ctor_get(v_x_5895_, 0);
lean_inc(v_maxSteps_5896_);
v_maxDischargeDepth_5897_ = lean_ctor_get(v_x_5895_, 1);
lean_inc(v_maxDischargeDepth_5897_);
v_contextual_5898_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3);
v_memoize_5899_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 1);
v_singlePass_5900_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 2);
v_zeta_5901_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 3);
v_beta_5902_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 4);
v_eta_5903_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 5);
v_etaStruct_5904_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 6);
v_iota_5905_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 7);
v_proj_5906_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 8);
v_decide_5907_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 9);
v_arith_5908_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 10);
v_autoUnfold_5909_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 11);
v_dsimp_5910_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5911_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 13);
v_ground_5912_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5913_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 15);
v_zetaDelta_5914_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 16);
v_index_5915_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5916_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 18);
v_zetaUnused_5917_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 19);
v_catchRuntime_5918_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 20);
v_zetaHave_5919_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 21);
v_letToHave_5920_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 22);
v_congrConsts_5921_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5922_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 24);
v_warnExponents_5923_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 25);
v_suggestions_5924_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 26);
v_maxSuggestions_5925_ = lean_ctor_get(v_x_5895_, 2);
lean_inc(v_maxSuggestions_5925_);
v_locals_5926_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 27);
v_instances_5927_ = lean_ctor_get_uint8(v_x_5895_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5895_);
v___x_5928_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5929_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5930_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5931_ = l_Nat_reprFast(v_maxSteps_5896_);
v___x_5932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5932_, 0, v___x_5931_);
v___x_5933_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5933_, 0, v___x_5930_);
lean_ctor_set(v___x_5933_, 1, v___x_5932_);
v___x_5934_ = 0;
v___x_5935_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5935_, 0, v___x_5933_);
lean_ctor_set_uint8(v___x_5935_, sizeof(void*)*1, v___x_5934_);
v___x_5936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5929_);
lean_ctor_set(v___x_5936_, 1, v___x_5935_);
v___x_5937_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5936_);
lean_ctor_set(v___x_5938_, 1, v___x_5937_);
v___x_5939_ = lean_box(1);
v___x_5940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5938_);
lean_ctor_set(v___x_5940_, 1, v___x_5939_);
v___x_5941_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_5942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5940_);
lean_ctor_set(v___x_5942_, 1, v___x_5941_);
v___x_5943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5943_, 0, v___x_5942_);
lean_ctor_set(v___x_5943_, 1, v___x_5928_);
v___x_5944_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_5945_ = l_Nat_reprFast(v_maxDischargeDepth_5897_);
v___x_5946_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5945_);
v___x_5947_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5947_, 0, v___x_5944_);
lean_ctor_set(v___x_5947_, 1, v___x_5946_);
v___x_5948_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5948_, 0, v___x_5947_);
lean_ctor_set_uint8(v___x_5948_, sizeof(void*)*1, v___x_5934_);
v___x_5949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5943_);
lean_ctor_set(v___x_5949_, 1, v___x_5948_);
v___x_5950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5949_);
lean_ctor_set(v___x_5950_, 1, v___x_5937_);
v___x_5951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5951_, 0, v___x_5950_);
lean_ctor_set(v___x_5951_, 1, v___x_5939_);
v___x_5952_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_5953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5953_, 0, v___x_5951_);
lean_ctor_set(v___x_5953_, 1, v___x_5952_);
v___x_5954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5954_, 0, v___x_5953_);
lean_ctor_set(v___x_5954_, 1, v___x_5928_);
v___x_5955_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5956_ = lean_unsigned_to_nat(0u);
v___x_5957_ = l_Bool_repr___redArg(v_contextual_5898_);
v___x_5958_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5958_, 0, v___x_5955_);
lean_ctor_set(v___x_5958_, 1, v___x_5957_);
v___x_5959_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5959_, 0, v___x_5958_);
lean_ctor_set_uint8(v___x_5959_, sizeof(void*)*1, v___x_5934_);
v___x_5960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5960_, 0, v___x_5954_);
lean_ctor_set(v___x_5960_, 1, v___x_5959_);
v___x_5961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5961_, 0, v___x_5960_);
lean_ctor_set(v___x_5961_, 1, v___x_5937_);
v___x_5962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5962_, 0, v___x_5961_);
lean_ctor_set(v___x_5962_, 1, v___x_5939_);
v___x_5963_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_5964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5964_, 0, v___x_5962_);
lean_ctor_set(v___x_5964_, 1, v___x_5963_);
v___x_5965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5964_);
lean_ctor_set(v___x_5965_, 1, v___x_5928_);
v___x_5966_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_5967_ = l_Bool_repr___redArg(v_memoize_5899_);
v___x_5968_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5966_);
lean_ctor_set(v___x_5968_, 1, v___x_5967_);
v___x_5969_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5969_, 0, v___x_5968_);
lean_ctor_set_uint8(v___x_5969_, sizeof(void*)*1, v___x_5934_);
v___x_5970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5970_, 0, v___x_5965_);
lean_ctor_set(v___x_5970_, 1, v___x_5969_);
v___x_5971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5971_, 0, v___x_5970_);
lean_ctor_set(v___x_5971_, 1, v___x_5937_);
v___x_5972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5971_);
lean_ctor_set(v___x_5972_, 1, v___x_5939_);
v___x_5973_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_5974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5972_);
lean_ctor_set(v___x_5974_, 1, v___x_5973_);
v___x_5975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5974_);
lean_ctor_set(v___x_5975_, 1, v___x_5928_);
v___x_5976_ = l_Bool_repr___redArg(v_singlePass_5900_);
v___x_5977_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5977_, 0, v___x_5955_);
lean_ctor_set(v___x_5977_, 1, v___x_5976_);
v___x_5978_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5978_, 0, v___x_5977_);
lean_ctor_set_uint8(v___x_5978_, sizeof(void*)*1, v___x_5934_);
v___x_5979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5975_);
lean_ctor_set(v___x_5979_, 1, v___x_5978_);
v___x_5980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5980_, 0, v___x_5979_);
lean_ctor_set(v___x_5980_, 1, v___x_5937_);
v___x_5981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5981_, 0, v___x_5980_);
lean_ctor_set(v___x_5981_, 1, v___x_5939_);
v___x_5982_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_5983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5983_, 0, v___x_5981_);
lean_ctor_set(v___x_5983_, 1, v___x_5982_);
v___x_5984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5984_, 0, v___x_5983_);
lean_ctor_set(v___x_5984_, 1, v___x_5928_);
v___x_5985_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5986_ = l_Bool_repr___redArg(v_zeta_5901_);
v___x_5987_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5987_, 0, v___x_5985_);
lean_ctor_set(v___x_5987_, 1, v___x_5986_);
v___x_5988_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5988_, 0, v___x_5987_);
lean_ctor_set_uint8(v___x_5988_, sizeof(void*)*1, v___x_5934_);
v___x_5989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5989_, 0, v___x_5984_);
lean_ctor_set(v___x_5989_, 1, v___x_5988_);
v___x_5990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5990_, 0, v___x_5989_);
lean_ctor_set(v___x_5990_, 1, v___x_5937_);
v___x_5991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5990_);
lean_ctor_set(v___x_5991_, 1, v___x_5939_);
v___x_5992_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5991_);
lean_ctor_set(v___x_5993_, 1, v___x_5992_);
v___x_5994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5994_, 0, v___x_5993_);
lean_ctor_set(v___x_5994_, 1, v___x_5928_);
v___x_5995_ = l_Bool_repr___redArg(v_beta_5902_);
v___x_5996_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5985_);
lean_ctor_set(v___x_5996_, 1, v___x_5995_);
v___x_5997_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5997_, 0, v___x_5996_);
lean_ctor_set_uint8(v___x_5997_, sizeof(void*)*1, v___x_5934_);
v___x_5998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5998_, 0, v___x_5994_);
lean_ctor_set(v___x_5998_, 1, v___x_5997_);
v___x_5999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5999_, 0, v___x_5998_);
lean_ctor_set(v___x_5999_, 1, v___x_5937_);
v___x_6000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6000_, 0, v___x_5999_);
lean_ctor_set(v___x_6000_, 1, v___x_5939_);
v___x_6001_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_6002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6002_, 0, v___x_6000_);
lean_ctor_set(v___x_6002_, 1, v___x_6001_);
v___x_6003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6003_, 0, v___x_6002_);
lean_ctor_set(v___x_6003_, 1, v___x_5928_);
v___x_6004_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_6005_ = l_Bool_repr___redArg(v_eta_5903_);
v___x_6006_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6004_);
lean_ctor_set(v___x_6006_, 1, v___x_6005_);
v___x_6007_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6007_, 0, v___x_6006_);
lean_ctor_set_uint8(v___x_6007_, sizeof(void*)*1, v___x_5934_);
v___x_6008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6008_, 0, v___x_6003_);
lean_ctor_set(v___x_6008_, 1, v___x_6007_);
v___x_6009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6009_, 0, v___x_6008_);
lean_ctor_set(v___x_6009_, 1, v___x_5937_);
v___x_6010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6010_, 0, v___x_6009_);
lean_ctor_set(v___x_6010_, 1, v___x_5939_);
v___x_6011_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_6012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6012_, 0, v___x_6010_);
lean_ctor_set(v___x_6012_, 1, v___x_6011_);
v___x_6013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6012_);
lean_ctor_set(v___x_6013_, 1, v___x_5928_);
v___x_6014_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_6015_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5904_, v___x_5956_);
v___x_6016_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6014_);
lean_ctor_set(v___x_6016_, 1, v___x_6015_);
v___x_6017_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6017_, 0, v___x_6016_);
lean_ctor_set_uint8(v___x_6017_, sizeof(void*)*1, v___x_5934_);
v___x_6018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6018_, 0, v___x_6013_);
lean_ctor_set(v___x_6018_, 1, v___x_6017_);
v___x_6019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6019_, 0, v___x_6018_);
lean_ctor_set(v___x_6019_, 1, v___x_5937_);
v___x_6020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6019_);
lean_ctor_set(v___x_6020_, 1, v___x_5939_);
v___x_6021_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_6022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6020_);
lean_ctor_set(v___x_6022_, 1, v___x_6021_);
v___x_6023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6022_);
lean_ctor_set(v___x_6023_, 1, v___x_5928_);
v___x_6024_ = l_Bool_repr___redArg(v_iota_5905_);
v___x_6025_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6025_, 0, v___x_5985_);
lean_ctor_set(v___x_6025_, 1, v___x_6024_);
v___x_6026_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6026_, 0, v___x_6025_);
lean_ctor_set_uint8(v___x_6026_, sizeof(void*)*1, v___x_5934_);
v___x_6027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6023_);
lean_ctor_set(v___x_6027_, 1, v___x_6026_);
v___x_6028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6028_, 0, v___x_6027_);
lean_ctor_set(v___x_6028_, 1, v___x_5937_);
v___x_6029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6029_, 0, v___x_6028_);
lean_ctor_set(v___x_6029_, 1, v___x_5939_);
v___x_6030_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_6031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6029_);
lean_ctor_set(v___x_6031_, 1, v___x_6030_);
v___x_6032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6032_, 0, v___x_6031_);
lean_ctor_set(v___x_6032_, 1, v___x_5928_);
v___x_6033_ = l_Bool_repr___redArg(v_proj_5906_);
v___x_6034_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___x_5985_);
lean_ctor_set(v___x_6034_, 1, v___x_6033_);
v___x_6035_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6035_, 0, v___x_6034_);
lean_ctor_set_uint8(v___x_6035_, sizeof(void*)*1, v___x_5934_);
v___x_6036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6032_);
lean_ctor_set(v___x_6036_, 1, v___x_6035_);
v___x_6037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6037_, 0, v___x_6036_);
lean_ctor_set(v___x_6037_, 1, v___x_5937_);
v___x_6038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6038_, 0, v___x_6037_);
lean_ctor_set(v___x_6038_, 1, v___x_5939_);
v___x_6039_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_6040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6038_);
lean_ctor_set(v___x_6040_, 1, v___x_6039_);
v___x_6041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6040_);
lean_ctor_set(v___x_6041_, 1, v___x_5928_);
v___x_6042_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_6043_ = l_Bool_repr___redArg(v_decide_5907_);
v___x_6044_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6044_, 0, v___x_6042_);
lean_ctor_set(v___x_6044_, 1, v___x_6043_);
v___x_6045_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6045_, 0, v___x_6044_);
lean_ctor_set_uint8(v___x_6045_, sizeof(void*)*1, v___x_5934_);
v___x_6046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6046_, 0, v___x_6041_);
lean_ctor_set(v___x_6046_, 1, v___x_6045_);
v___x_6047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6047_, 0, v___x_6046_);
lean_ctor_set(v___x_6047_, 1, v___x_5937_);
v___x_6048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6048_, 0, v___x_6047_);
lean_ctor_set(v___x_6048_, 1, v___x_5939_);
v___x_6049_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_6050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6048_);
lean_ctor_set(v___x_6050_, 1, v___x_6049_);
v___x_6051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6051_, 0, v___x_6050_);
lean_ctor_set(v___x_6051_, 1, v___x_5928_);
v___x_6052_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_6053_ = l_Bool_repr___redArg(v_arith_5908_);
v___x_6054_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6052_);
lean_ctor_set(v___x_6054_, 1, v___x_6053_);
v___x_6055_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6055_, 0, v___x_6054_);
lean_ctor_set_uint8(v___x_6055_, sizeof(void*)*1, v___x_5934_);
v___x_6056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6056_, 0, v___x_6051_);
lean_ctor_set(v___x_6056_, 1, v___x_6055_);
v___x_6057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6057_, 0, v___x_6056_);
lean_ctor_set(v___x_6057_, 1, v___x_5937_);
v___x_6058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6058_, 0, v___x_6057_);
lean_ctor_set(v___x_6058_, 1, v___x_5939_);
v___x_6059_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_6060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6058_);
lean_ctor_set(v___x_6060_, 1, v___x_6059_);
v___x_6061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6060_);
lean_ctor_set(v___x_6061_, 1, v___x_5928_);
v___x_6062_ = l_Bool_repr___redArg(v_autoUnfold_5909_);
v___x_6063_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6063_, 0, v___x_5955_);
lean_ctor_set(v___x_6063_, 1, v___x_6062_);
v___x_6064_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6064_, 0, v___x_6063_);
lean_ctor_set_uint8(v___x_6064_, sizeof(void*)*1, v___x_5934_);
v___x_6065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6061_);
lean_ctor_set(v___x_6065_, 1, v___x_6064_);
v___x_6066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6065_);
lean_ctor_set(v___x_6066_, 1, v___x_5937_);
v___x_6067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6067_, 0, v___x_6066_);
lean_ctor_set(v___x_6067_, 1, v___x_5939_);
v___x_6068_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_6069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6067_);
lean_ctor_set(v___x_6069_, 1, v___x_6068_);
v___x_6070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6069_);
lean_ctor_set(v___x_6070_, 1, v___x_5928_);
v___x_6071_ = l_Bool_repr___redArg(v_dsimp_5910_);
v___x_6072_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6052_);
lean_ctor_set(v___x_6072_, 1, v___x_6071_);
v___x_6073_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6073_, 0, v___x_6072_);
lean_ctor_set_uint8(v___x_6073_, sizeof(void*)*1, v___x_5934_);
v___x_6074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6074_, 0, v___x_6070_);
lean_ctor_set(v___x_6074_, 1, v___x_6073_);
v___x_6075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6075_, 0, v___x_6074_);
lean_ctor_set(v___x_6075_, 1, v___x_5937_);
v___x_6076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6076_, 0, v___x_6075_);
lean_ctor_set(v___x_6076_, 1, v___x_5939_);
v___x_6077_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_6078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6076_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6079_, 0, v___x_6078_);
lean_ctor_set(v___x_6079_, 1, v___x_5928_);
v___x_6080_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_6081_ = l_Bool_repr___redArg(v_failIfUnchanged_5911_);
v___x_6082_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6080_);
lean_ctor_set(v___x_6082_, 1, v___x_6081_);
v___x_6083_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6083_, 0, v___x_6082_);
lean_ctor_set_uint8(v___x_6083_, sizeof(void*)*1, v___x_5934_);
v___x_6084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6084_, 0, v___x_6079_);
lean_ctor_set(v___x_6084_, 1, v___x_6083_);
v___x_6085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6085_, 0, v___x_6084_);
lean_ctor_set(v___x_6085_, 1, v___x_5937_);
v___x_6086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6085_);
lean_ctor_set(v___x_6086_, 1, v___x_5939_);
v___x_6087_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_6088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6088_, 0, v___x_6086_);
lean_ctor_set(v___x_6088_, 1, v___x_6087_);
v___x_6089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6088_);
lean_ctor_set(v___x_6089_, 1, v___x_5928_);
v___x_6090_ = l_Bool_repr___redArg(v_ground_5912_);
v___x_6091_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6042_);
lean_ctor_set(v___x_6091_, 1, v___x_6090_);
v___x_6092_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6092_, 0, v___x_6091_);
lean_ctor_set_uint8(v___x_6092_, sizeof(void*)*1, v___x_5934_);
v___x_6093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6089_);
lean_ctor_set(v___x_6093_, 1, v___x_6092_);
v___x_6094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___x_6093_);
lean_ctor_set(v___x_6094_, 1, v___x_5937_);
v___x_6095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6094_);
lean_ctor_set(v___x_6095_, 1, v___x_5939_);
v___x_6096_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_6097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6097_, 0, v___x_6095_);
lean_ctor_set(v___x_6097_, 1, v___x_6096_);
v___x_6098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6097_);
lean_ctor_set(v___x_6098_, 1, v___x_5928_);
v___x_6099_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_6100_ = l_Bool_repr___redArg(v_unfoldPartialApp_5913_);
v___x_6101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6099_);
lean_ctor_set(v___x_6101_, 1, v___x_6100_);
v___x_6102_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
lean_ctor_set_uint8(v___x_6102_, sizeof(void*)*1, v___x_5934_);
v___x_6103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6098_);
lean_ctor_set(v___x_6103_, 1, v___x_6102_);
v___x_6104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
lean_ctor_set(v___x_6104_, 1, v___x_5937_);
v___x_6105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6105_, 0, v___x_6104_);
lean_ctor_set(v___x_6105_, 1, v___x_5939_);
v___x_6106_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6107_, 0, v___x_6105_);
lean_ctor_set(v___x_6107_, 1, v___x_6106_);
v___x_6108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6108_, 0, v___x_6107_);
lean_ctor_set(v___x_6108_, 1, v___x_5928_);
v___x_6109_ = l_Bool_repr___redArg(v_zetaDelta_5914_);
v___x_6110_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6110_, 0, v___x_6014_);
lean_ctor_set(v___x_6110_, 1, v___x_6109_);
v___x_6111_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6111_, 0, v___x_6110_);
lean_ctor_set_uint8(v___x_6111_, sizeof(void*)*1, v___x_5934_);
v___x_6112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6112_, 0, v___x_6108_);
lean_ctor_set(v___x_6112_, 1, v___x_6111_);
v___x_6113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6112_);
lean_ctor_set(v___x_6113_, 1, v___x_5937_);
v___x_6114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6114_, 0, v___x_6113_);
lean_ctor_set(v___x_6114_, 1, v___x_5939_);
v___x_6115_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6114_);
lean_ctor_set(v___x_6116_, 1, v___x_6115_);
v___x_6117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6116_);
lean_ctor_set(v___x_6117_, 1, v___x_5928_);
v___x_6118_ = l_Bool_repr___redArg(v_index_5915_);
v___x_6119_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6119_, 0, v___x_6052_);
lean_ctor_set(v___x_6119_, 1, v___x_6118_);
v___x_6120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6120_, 0, v___x_6119_);
lean_ctor_set_uint8(v___x_6120_, sizeof(void*)*1, v___x_5934_);
v___x_6121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6121_, 0, v___x_6117_);
lean_ctor_set(v___x_6121_, 1, v___x_6120_);
v___x_6122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6122_, 0, v___x_6121_);
lean_ctor_set(v___x_6122_, 1, v___x_5937_);
v___x_6123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6123_, 0, v___x_6122_);
lean_ctor_set(v___x_6123_, 1, v___x_5939_);
v___x_6124_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6125_, 0, v___x_6123_);
lean_ctor_set(v___x_6125_, 1, v___x_6124_);
v___x_6126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6126_, 0, v___x_6125_);
lean_ctor_set(v___x_6126_, 1, v___x_5928_);
v___x_6127_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6128_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5916_);
v___x_6129_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6127_);
lean_ctor_set(v___x_6129_, 1, v___x_6128_);
v___x_6130_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6130_, 0, v___x_6129_);
lean_ctor_set_uint8(v___x_6130_, sizeof(void*)*1, v___x_5934_);
v___x_6131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6131_, 0, v___x_6126_);
lean_ctor_set(v___x_6131_, 1, v___x_6130_);
v___x_6132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6131_);
lean_ctor_set(v___x_6132_, 1, v___x_5937_);
v___x_6133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6132_);
lean_ctor_set(v___x_6133_, 1, v___x_5939_);
v___x_6134_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6135_, 0, v___x_6133_);
lean_ctor_set(v___x_6135_, 1, v___x_6134_);
v___x_6136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6136_, 0, v___x_6135_);
lean_ctor_set(v___x_6136_, 1, v___x_5928_);
v___x_6137_ = l_Bool_repr___redArg(v_zetaUnused_5917_);
v___x_6138_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6138_, 0, v___x_5955_);
lean_ctor_set(v___x_6138_, 1, v___x_6137_);
v___x_6139_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6139_, 0, v___x_6138_);
lean_ctor_set_uint8(v___x_6139_, sizeof(void*)*1, v___x_5934_);
v___x_6140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6140_, 0, v___x_6136_);
lean_ctor_set(v___x_6140_, 1, v___x_6139_);
v___x_6141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6141_, 0, v___x_6140_);
lean_ctor_set(v___x_6141_, 1, v___x_5937_);
v___x_6142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6142_, 0, v___x_6141_);
lean_ctor_set(v___x_6142_, 1, v___x_5939_);
v___x_6143_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6142_);
lean_ctor_set(v___x_6144_, 1, v___x_6143_);
v___x_6145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6145_, 0, v___x_6144_);
lean_ctor_set(v___x_6145_, 1, v___x_5928_);
v___x_6146_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6147_ = l_Bool_repr___redArg(v_catchRuntime_5918_);
v___x_6148_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6146_);
lean_ctor_set(v___x_6148_, 1, v___x_6147_);
v___x_6149_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6149_, 0, v___x_6148_);
lean_ctor_set_uint8(v___x_6149_, sizeof(void*)*1, v___x_5934_);
v___x_6150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6150_, 0, v___x_6145_);
lean_ctor_set(v___x_6150_, 1, v___x_6149_);
v___x_6151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6151_, 0, v___x_6150_);
lean_ctor_set(v___x_6151_, 1, v___x_5937_);
v___x_6152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6152_, 0, v___x_6151_);
lean_ctor_set(v___x_6152_, 1, v___x_5939_);
v___x_6153_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6154_, 0, v___x_6152_);
lean_ctor_set(v___x_6154_, 1, v___x_6153_);
v___x_6155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6155_, 0, v___x_6154_);
lean_ctor_set(v___x_6155_, 1, v___x_5928_);
v___x_6156_ = l_Bool_repr___redArg(v_zetaHave_5919_);
v___x_6157_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6157_, 0, v___x_5930_);
lean_ctor_set(v___x_6157_, 1, v___x_6156_);
v___x_6158_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6158_, 0, v___x_6157_);
lean_ctor_set_uint8(v___x_6158_, sizeof(void*)*1, v___x_5934_);
v___x_6159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6155_);
lean_ctor_set(v___x_6159_, 1, v___x_6158_);
v___x_6160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6160_, 0, v___x_6159_);
lean_ctor_set(v___x_6160_, 1, v___x_5937_);
v___x_6161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6161_, 0, v___x_6160_);
lean_ctor_set(v___x_6161_, 1, v___x_5939_);
v___x_6162_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6163_, 0, v___x_6161_);
lean_ctor_set(v___x_6163_, 1, v___x_6162_);
v___x_6164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6164_, 0, v___x_6163_);
lean_ctor_set(v___x_6164_, 1, v___x_5928_);
v___x_6165_ = l_Bool_repr___redArg(v_letToHave_5920_);
v___x_6166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6166_, 0, v___x_6014_);
lean_ctor_set(v___x_6166_, 1, v___x_6165_);
v___x_6167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6167_, 0, v___x_6166_);
lean_ctor_set_uint8(v___x_6167_, sizeof(void*)*1, v___x_5934_);
v___x_6168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6168_, 0, v___x_6164_);
lean_ctor_set(v___x_6168_, 1, v___x_6167_);
v___x_6169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6169_, 0, v___x_6168_);
lean_ctor_set(v___x_6169_, 1, v___x_5937_);
v___x_6170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6170_, 0, v___x_6169_);
lean_ctor_set(v___x_6170_, 1, v___x_5939_);
v___x_6171_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6172_, 0, v___x_6170_);
lean_ctor_set(v___x_6172_, 1, v___x_6171_);
v___x_6173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6173_, 0, v___x_6172_);
lean_ctor_set(v___x_6173_, 1, v___x_5928_);
v___x_6174_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6175_ = l_Bool_repr___redArg(v_congrConsts_5921_);
v___x_6176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6174_);
lean_ctor_set(v___x_6176_, 1, v___x_6175_);
v___x_6177_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6177_, 0, v___x_6176_);
lean_ctor_set_uint8(v___x_6177_, sizeof(void*)*1, v___x_5934_);
v___x_6178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6178_, 0, v___x_6173_);
lean_ctor_set(v___x_6178_, 1, v___x_6177_);
v___x_6179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6178_);
lean_ctor_set(v___x_6179_, 1, v___x_5937_);
v___x_6180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6180_, 0, v___x_6179_);
lean_ctor_set(v___x_6180_, 1, v___x_5939_);
v___x_6181_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6182_, 0, v___x_6180_);
lean_ctor_set(v___x_6182_, 1, v___x_6181_);
v___x_6183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6183_, 0, v___x_6182_);
lean_ctor_set(v___x_6183_, 1, v___x_5928_);
v___x_6184_ = l_Bool_repr___redArg(v_bitVecOfNat_5922_);
v___x_6185_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6185_, 0, v___x_6174_);
lean_ctor_set(v___x_6185_, 1, v___x_6184_);
v___x_6186_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6186_, 0, v___x_6185_);
lean_ctor_set_uint8(v___x_6186_, sizeof(void*)*1, v___x_5934_);
v___x_6187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6187_, 0, v___x_6183_);
lean_ctor_set(v___x_6187_, 1, v___x_6186_);
v___x_6188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6188_, 0, v___x_6187_);
lean_ctor_set(v___x_6188_, 1, v___x_5937_);
v___x_6189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6189_, 0, v___x_6188_);
lean_ctor_set(v___x_6189_, 1, v___x_5939_);
v___x_6190_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6191_, 0, v___x_6189_);
lean_ctor_set(v___x_6191_, 1, v___x_6190_);
v___x_6192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6192_, 0, v___x_6191_);
lean_ctor_set(v___x_6192_, 1, v___x_5928_);
v___x_6193_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6194_ = l_Bool_repr___redArg(v_warnExponents_5923_);
v___x_6195_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6195_, 0, v___x_6193_);
lean_ctor_set(v___x_6195_, 1, v___x_6194_);
v___x_6196_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6196_, 0, v___x_6195_);
lean_ctor_set_uint8(v___x_6196_, sizeof(void*)*1, v___x_5934_);
v___x_6197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6197_, 0, v___x_6192_);
lean_ctor_set(v___x_6197_, 1, v___x_6196_);
v___x_6198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6198_, 0, v___x_6197_);
lean_ctor_set(v___x_6198_, 1, v___x_5937_);
v___x_6199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6199_, 0, v___x_6198_);
lean_ctor_set(v___x_6199_, 1, v___x_5939_);
v___x_6200_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6201_, 0, v___x_6199_);
lean_ctor_set(v___x_6201_, 1, v___x_6200_);
v___x_6202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6202_, 0, v___x_6201_);
lean_ctor_set(v___x_6202_, 1, v___x_5928_);
v___x_6203_ = l_Bool_repr___redArg(v_suggestions_5924_);
v___x_6204_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6204_, 0, v___x_6174_);
lean_ctor_set(v___x_6204_, 1, v___x_6203_);
v___x_6205_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6205_, 0, v___x_6204_);
lean_ctor_set_uint8(v___x_6205_, sizeof(void*)*1, v___x_5934_);
v___x_6206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6206_, 0, v___x_6202_);
lean_ctor_set(v___x_6206_, 1, v___x_6205_);
v___x_6207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6207_, 0, v___x_6206_);
lean_ctor_set(v___x_6207_, 1, v___x_5937_);
v___x_6208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6208_, 0, v___x_6207_);
lean_ctor_set(v___x_6208_, 1, v___x_5939_);
v___x_6209_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6210_, 0, v___x_6208_);
lean_ctor_set(v___x_6210_, 1, v___x_6209_);
v___x_6211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6211_, 0, v___x_6210_);
lean_ctor_set(v___x_6211_, 1, v___x_5928_);
v___x_6212_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6213_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5925_, v___x_5956_);
v___x_6214_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6214_, 0, v___x_6212_);
lean_ctor_set(v___x_6214_, 1, v___x_6213_);
v___x_6215_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6215_, 0, v___x_6214_);
lean_ctor_set_uint8(v___x_6215_, sizeof(void*)*1, v___x_5934_);
v___x_6216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6216_, 0, v___x_6211_);
lean_ctor_set(v___x_6216_, 1, v___x_6215_);
v___x_6217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6217_, 0, v___x_6216_);
lean_ctor_set(v___x_6217_, 1, v___x_5937_);
v___x_6218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6218_, 0, v___x_6217_);
lean_ctor_set(v___x_6218_, 1, v___x_5939_);
v___x_6219_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6220_, 0, v___x_6218_);
lean_ctor_set(v___x_6220_, 1, v___x_6219_);
v___x_6221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6221_, 0, v___x_6220_);
lean_ctor_set(v___x_6221_, 1, v___x_5928_);
v___x_6222_ = l_Bool_repr___redArg(v_locals_5926_);
v___x_6223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6223_, 0, v___x_6042_);
lean_ctor_set(v___x_6223_, 1, v___x_6222_);
v___x_6224_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6224_, 0, v___x_6223_);
lean_ctor_set_uint8(v___x_6224_, sizeof(void*)*1, v___x_5934_);
v___x_6225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6225_, 0, v___x_6221_);
lean_ctor_set(v___x_6225_, 1, v___x_6224_);
v___x_6226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6226_, 0, v___x_6225_);
lean_ctor_set(v___x_6226_, 1, v___x_5937_);
v___x_6227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6227_, 0, v___x_6226_);
lean_ctor_set(v___x_6227_, 1, v___x_5939_);
v___x_6228_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6229_, 0, v___x_6227_);
lean_ctor_set(v___x_6229_, 1, v___x_6228_);
v___x_6230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6230_, 0, v___x_6229_);
lean_ctor_set(v___x_6230_, 1, v___x_5928_);
v___x_6231_ = l_Bool_repr___redArg(v_instances_5927_);
v___x_6232_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6232_, 0, v___x_6014_);
lean_ctor_set(v___x_6232_, 1, v___x_6231_);
v___x_6233_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6233_, 0, v___x_6232_);
lean_ctor_set_uint8(v___x_6233_, sizeof(void*)*1, v___x_5934_);
v___x_6234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6234_, 0, v___x_6230_);
lean_ctor_set(v___x_6234_, 1, v___x_6233_);
v___x_6235_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6236_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6237_, 0, v___x_6236_);
lean_ctor_set(v___x_6237_, 1, v___x_6234_);
v___x_6238_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6239_, 0, v___x_6237_);
lean_ctor_set(v___x_6239_, 1, v___x_6238_);
v___x_6240_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6240_, 0, v___x_6235_);
lean_ctor_set(v___x_6240_, 1, v___x_6239_);
v___x_6241_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6241_, 0, v___x_6240_);
lean_ctor_set_uint8(v___x_6241_, sizeof(void*)*1, v___x_5934_);
return v___x_6241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6242_, lean_object* v_prec_6243_){
_start:
{
lean_object* v___x_6244_; 
v___x_6244_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6242_);
return v___x_6244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6245_, lean_object* v_prec_6246_){
_start:
{
lean_object* v_res_6247_; 
v_res_6247_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6245_, v_prec_6246_);
lean_dec(v_prec_6246_);
return v_res_6247_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6250_, lean_object* v_x_6251_){
_start:
{
if (lean_obj_tag(v_x_6251_) == 0)
{
uint8_t v___x_6252_; 
v___x_6252_ = 0;
return v___x_6252_;
}
else
{
lean_object* v_head_6253_; lean_object* v_tail_6254_; uint8_t v___x_6255_; 
v_head_6253_ = lean_ctor_get(v_x_6251_, 0);
v_tail_6254_ = lean_ctor_get(v_x_6251_, 1);
v___x_6255_ = lean_nat_dec_eq(v_a_6250_, v_head_6253_);
if (v___x_6255_ == 0)
{
v_x_6251_ = v_tail_6254_;
goto _start;
}
else
{
return v___x_6255_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6257_, lean_object* v_x_6258_){
_start:
{
uint8_t v_res_6259_; lean_object* v_r_6260_; 
v_res_6259_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6257_, v_x_6258_);
lean_dec(v_x_6258_);
lean_dec(v_a_6257_);
v_r_6260_ = lean_box(v_res_6259_);
return v_r_6260_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6261_, lean_object* v_x_6262_){
_start:
{
switch(lean_obj_tag(v_x_6261_))
{
case 0:
{
uint8_t v___x_6263_; 
v___x_6263_ = 1;
return v___x_6263_;
}
case 1:
{
lean_object* v_idxs_6264_; uint8_t v___x_6265_; 
v_idxs_6264_ = lean_ctor_get(v_x_6261_, 0);
v___x_6265_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6262_, v_idxs_6264_);
return v___x_6265_;
}
default: 
{
lean_object* v_idxs_6266_; uint8_t v___x_6267_; 
v_idxs_6266_ = lean_ctor_get(v_x_6261_, 0);
v___x_6267_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6262_, v_idxs_6266_);
if (v___x_6267_ == 0)
{
uint8_t v___x_6268_; 
v___x_6268_ = 1;
return v___x_6268_;
}
else
{
uint8_t v___x_6269_; 
v___x_6269_ = 0;
return v___x_6269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6270_, lean_object* v_x_6271_){
_start:
{
uint8_t v_res_6272_; lean_object* v_r_6273_; 
v_res_6272_ = l_Lean_Meta_Occurrences_contains(v_x_6270_, v_x_6271_);
lean_dec(v_x_6271_);
lean_dec(v_x_6270_);
v_r_6273_ = lean_box(v_res_6272_);
return v_r_6273_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6274_){
_start:
{
if (lean_obj_tag(v_x_6274_) == 0)
{
uint8_t v___x_6275_; 
v___x_6275_ = 1;
return v___x_6275_;
}
else
{
uint8_t v___x_6276_; 
v___x_6276_ = 0;
return v___x_6276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6277_){
_start:
{
uint8_t v_res_6278_; lean_object* v_r_6279_; 
v_res_6278_ = l_Lean_Meta_Occurrences_isAll(v_x_6277_);
lean_dec(v_x_6277_);
v_r_6279_ = lean_box(v_res_6278_);
return v_r_6279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t v_x_6280_){
_start:
{
switch(v_x_6280_)
{
case 0:
{
lean_object* v___x_6281_; 
v___x_6281_ = lean_unsigned_to_nat(0u);
return v___x_6281_;
}
case 1:
{
lean_object* v___x_6282_; 
v___x_6282_ = lean_unsigned_to_nat(1u);
return v___x_6282_;
}
default: 
{
lean_object* v___x_6283_; 
v___x_6283_ = lean_unsigned_to_nat(2u);
return v___x_6283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object* v_x_6284_){
_start:
{
uint8_t v_x_boxed_6285_; lean_object* v_res_6286_; 
v_x_boxed_6285_ = lean_unbox(v_x_6284_);
v_res_6286_ = l_Lean_Meta_ApplyNewGoals_ctorIdx(v_x_boxed_6285_);
return v_res_6286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6287_){
_start:
{
lean_inc(v_k_6287_);
return v_k_6287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6288_){
_start:
{
lean_object* v_res_6289_; 
v_res_6289_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6288_);
lean_dec(v_k_6288_);
return v_res_6289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6290_, lean_object* v_ctorIdx_6291_, uint8_t v_t_6292_, lean_object* v_h_6293_, lean_object* v_k_6294_){
_start:
{
lean_inc(v_k_6294_);
return v_k_6294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6295_, lean_object* v_ctorIdx_6296_, lean_object* v_t_6297_, lean_object* v_h_6298_, lean_object* v_k_6299_){
_start:
{
uint8_t v_t_boxed_6300_; lean_object* v_res_6301_; 
v_t_boxed_6300_ = lean_unbox(v_t_6297_);
v_res_6301_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6295_, v_ctorIdx_6296_, v_t_boxed_6300_, v_h_6298_, v_k_6299_);
lean_dec(v_k_6299_);
lean_dec(v_ctorIdx_6296_);
return v_res_6301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6302_){
_start:
{
lean_inc(v_nonDependentFirst_6302_);
return v_nonDependentFirst_6302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6303_){
_start:
{
lean_object* v_res_6304_; 
v_res_6304_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6303_);
lean_dec(v_nonDependentFirst_6303_);
return v_res_6304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6305_, uint8_t v_t_6306_, lean_object* v_h_6307_, lean_object* v_nonDependentFirst_6308_){
_start:
{
lean_inc(v_nonDependentFirst_6308_);
return v_nonDependentFirst_6308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6309_, lean_object* v_t_6310_, lean_object* v_h_6311_, lean_object* v_nonDependentFirst_6312_){
_start:
{
uint8_t v_t_boxed_6313_; lean_object* v_res_6314_; 
v_t_boxed_6313_ = lean_unbox(v_t_6310_);
v_res_6314_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6309_, v_t_boxed_6313_, v_h_6311_, v_nonDependentFirst_6312_);
lean_dec(v_nonDependentFirst_6312_);
return v_res_6314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6315_){
_start:
{
lean_inc(v_nonDependentOnly_6315_);
return v_nonDependentOnly_6315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6316_){
_start:
{
lean_object* v_res_6317_; 
v_res_6317_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6316_);
lean_dec(v_nonDependentOnly_6316_);
return v_res_6317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6318_, uint8_t v_t_6319_, lean_object* v_h_6320_, lean_object* v_nonDependentOnly_6321_){
_start:
{
lean_inc(v_nonDependentOnly_6321_);
return v_nonDependentOnly_6321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6322_, lean_object* v_t_6323_, lean_object* v_h_6324_, lean_object* v_nonDependentOnly_6325_){
_start:
{
uint8_t v_t_boxed_6326_; lean_object* v_res_6327_; 
v_t_boxed_6326_ = lean_unbox(v_t_6323_);
v_res_6327_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6322_, v_t_boxed_6326_, v_h_6324_, v_nonDependentOnly_6325_);
lean_dec(v_nonDependentOnly_6325_);
return v_res_6327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6328_){
_start:
{
lean_inc(v_all_6328_);
return v_all_6328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6329_){
_start:
{
lean_object* v_res_6330_; 
v_res_6330_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6329_);
lean_dec(v_all_6329_);
return v_res_6330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6331_, uint8_t v_t_6332_, lean_object* v_h_6333_, lean_object* v_all_6334_){
_start:
{
lean_inc(v_all_6334_);
return v_all_6334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6335_, lean_object* v_t_6336_, lean_object* v_h_6337_, lean_object* v_all_6338_){
_start:
{
uint8_t v_t_boxed_6339_; lean_object* v_res_6340_; 
v_t_boxed_6339_ = lean_unbox(v_t_6336_);
v_res_6340_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6335_, v_t_boxed_6339_, v_h_6337_, v_all_6338_);
lean_dec(v_all_6338_);
return v_res_6340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6354_){
_start:
{
lean_object* v___x_6355_; uint8_t v___x_6356_; 
v___x_6355_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6354_);
v___x_6356_ = l_Lean_Syntax_isOfKind(v_c_6354_, v___x_6355_);
if (v___x_6356_ == 0)
{
lean_object* v___x_6357_; uint8_t v___x_6358_; 
v___x_6357_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6354_);
v___x_6358_ = l_Lean_Syntax_isOfKind(v_c_6354_, v___x_6357_);
if (v___x_6358_ == 0)
{
lean_object* v___x_6359_; uint8_t v___x_6360_; 
v___x_6359_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6354_);
v___x_6360_ = l_Lean_Syntax_isOfKind(v_c_6354_, v___x_6359_);
if (v___x_6360_ == 0)
{
lean_object* v___x_6361_; 
lean_dec(v_c_6354_);
v___x_6361_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6361_;
}
else
{
lean_object* v___x_6362_; lean_object* v___x_6363_; lean_object* v___x_6364_; 
v___x_6362_ = lean_unsigned_to_nat(1u);
v___x_6363_ = lean_mk_empty_array_with_capacity(v___x_6362_);
v___x_6364_ = lean_array_push(v___x_6363_, v_c_6354_);
return v___x_6364_;
}
}
else
{
lean_object* v___x_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; 
v___x_6365_ = lean_unsigned_to_nat(0u);
v___x_6366_ = l_Lean_Syntax_getArg(v_c_6354_, v___x_6365_);
lean_dec(v_c_6354_);
v___x_6367_ = l_Lean_Syntax_getArgs(v___x_6366_);
lean_dec(v___x_6366_);
return v___x_6367_;
}
}
else
{
lean_object* v___x_6368_; lean_object* v___x_6369_; lean_object* v___x_6370_; lean_object* v___x_6371_; uint8_t v___x_6372_; 
v___x_6368_ = l_Lean_Syntax_getArgs(v_c_6354_);
lean_dec(v_c_6354_);
v___x_6369_ = lean_unsigned_to_nat(0u);
v___x_6370_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6371_ = lean_array_get_size(v___x_6368_);
v___x_6372_ = lean_nat_dec_lt(v___x_6369_, v___x_6371_);
if (v___x_6372_ == 0)
{
lean_dec_ref(v___x_6368_);
return v___x_6370_;
}
else
{
size_t v___x_6373_; size_t v___x_6374_; lean_object* v___x_6375_; 
v___x_6373_ = ((size_t)0ULL);
v___x_6374_ = lean_usize_of_nat(v___x_6371_);
v___x_6375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6368_, v___x_6373_, v___x_6374_, v___x_6370_);
lean_dec_ref(v___x_6368_);
return v___x_6375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6376_, size_t v_i_6377_, size_t v_stop_6378_, lean_object* v_b_6379_){
_start:
{
uint8_t v___x_6380_; 
v___x_6380_ = lean_usize_dec_eq(v_i_6377_, v_stop_6378_);
if (v___x_6380_ == 0)
{
lean_object* v___x_6381_; lean_object* v___x_6382_; lean_object* v___x_6383_; size_t v___x_6384_; size_t v___x_6385_; 
v___x_6381_ = lean_array_uget_borrowed(v_as_6376_, v_i_6377_);
lean_inc(v___x_6381_);
v___x_6382_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6381_);
v___x_6383_ = l_Array_append___redArg(v_b_6379_, v___x_6382_);
lean_dec_ref(v___x_6382_);
v___x_6384_ = ((size_t)1ULL);
v___x_6385_ = lean_usize_add(v_i_6377_, v___x_6384_);
v_i_6377_ = v___x_6385_;
v_b_6379_ = v___x_6383_;
goto _start;
}
else
{
return v_b_6379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6387_, lean_object* v_i_6388_, lean_object* v_stop_6389_, lean_object* v_b_6390_){
_start:
{
size_t v_i_boxed_6391_; size_t v_stop_boxed_6392_; lean_object* v_res_6393_; 
v_i_boxed_6391_ = lean_unbox_usize(v_i_6388_);
lean_dec(v_i_6388_);
v_stop_boxed_6392_ = lean_unbox_usize(v_stop_6389_);
lean_dec(v_stop_6389_);
v_res_6393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6387_, v_i_boxed_6391_, v_stop_boxed_6392_, v_b_6390_);
lean_dec_ref(v_as_6387_);
return v_res_6393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6394_){
_start:
{
lean_object* v___x_6395_; lean_object* v___x_6396_; lean_object* v___x_6397_; lean_object* v___x_6398_; lean_object* v___x_6399_; 
v___x_6395_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6396_ = lean_box(2);
v___x_6397_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6398_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6398_, 0, v___x_6396_);
lean_ctor_set(v___x_6398_, 1, v___x_6397_);
lean_ctor_set(v___x_6398_, 2, v_items_6394_);
v___x_6399_ = l_Lean_Syntax_node1(v___x_6396_, v___x_6395_, v___x_6398_);
return v___x_6399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6400_, lean_object* v_cfg_x27_6401_){
_start:
{
lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; 
v___x_6402_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6400_);
v___x_6403_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6401_);
v___x_6404_ = l_Array_append___redArg(v___x_6402_, v___x_6403_);
lean_dec_ref(v___x_6403_);
v___x_6405_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6404_);
return v___x_6405_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1 = _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1);
l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2 = _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2);
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
