// Lean compiler output
// Module: Lake.Util.Git
// Imports: public import Init.Data.ToString public import Lake.Util.Proc import Init.Data.String.TakeDrop import Init.Data.String.Search
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_captureProc_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_testProc(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lake_Git_defaultRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "origin"};
static const lean_object* l_Lake_Git_defaultRemote___closed__0 = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_defaultRemote = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
static const lean_string_object l_Lake_Git_upstreamBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "master"};
static const lean_object* l_Lake_Git_upstreamBranch___closed__0 = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_upstreamBranch = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ".git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__0 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__0_value;
static lean_once_cell_t l_Lake_Git_filterUrl_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__1;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__2 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__2_value;
static lean_once_cell_t l_Lake_Git_filterUrl_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Git_isFullObjectName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Git_isFullObjectName_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instCoeFilePathGitRepo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoeFilePathGitRepo___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeFilePathGitRepo___closed__0 = (const lean_object*)&l_Lake_instCoeFilePathGitRepo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeFilePathGitRepo = (const lean_object*)&l_Lake_instCoeFilePathGitRepo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToStringGitRepo = (const lean_object*)&l_Lake_instCoeFilePathGitRepo___closed__0_value;
static const lean_string_object l_Lake_GitRepo_cwd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_GitRepo_cwd___closed__0 = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_cwd = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_GitRepo_captureGit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__0 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__0_value;
static const lean_array_object l_Lake_GitRepo_captureGit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__1 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_clone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clone"};
static const lean_object* l_Lake_GitRepo_clone___closed__0 = (const lean_object*)&l_Lake_GitRepo_clone___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_clone___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_clone___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_quietInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__0 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value;
static const lean_string_object l_Lake_GitRepo_quietInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-q"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__1 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value;
static const lean_array_object l_Lake_GitRepo_quietInit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_quietInit___closed__2 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rev-parse"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__0 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value;
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "--is-inside-work-tree"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__1 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value;
static const lean_array_object l_Lake_GitRepo_insideWorkTree___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value),((lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__2 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_fetch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "fetch"};
static const lean_object* l_Lake_GitRepo_fetch___closed__0 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--tags"};
static const lean_object* l_Lake_GitRepo_fetch___closed__1 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__1_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--force"};
static const lean_object* l_Lake_GitRepo_fetch___closed__2 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__3;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__4;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__5;
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "checkout"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-B"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__1 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_checkoutBranch___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__2;
static lean_once_cell_t l_Lake_GitRepo_checkoutBranch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutDetach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--detach"};
static const lean_object* l_Lake_GitRepo_checkoutDetach___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutDetach___closed__0_value;
static const lean_string_object l_Lake_GitRepo_checkoutDetach___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l_Lake_GitRepo_checkoutDetach___closed__1 = (const lean_object*)&l_Lake_GitRepo_checkoutDetach___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_checkoutDetach___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__2;
static lean_once_cell_t l_Lake_GitRepo_checkoutDetach___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--verify"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "--end-of-options"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ": revision not found '"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Lake_GitRepo_getHeadRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevision_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = ": could not resolve 'HEAD' to a commit; the repository may be corrupt, so you may need to remove it and try again"};
static const lean_object* l_Lake_GitRepo_getHeadRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevision___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rev-list"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value;
static const lean_array_object l_Lake_GitRepo_getHeadRevisions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value),((lean_object*)&l_Lake_GitRepo_getHeadRevision_x3f___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__1 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__1_value;
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-n"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__2 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_getHeadRevisions___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getHeadRevisions___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRemoteRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_GitRepo_resolveRemoteRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRemoteRevision___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_branchExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "show-ref"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__0 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__0_value;
static const lean_string_object l_Lake_GitRepo_branchExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "refs/heads/"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__1 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_branchExists___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_branchExists___closed__2;
static lean_once_cell_t l_Lake_GitRepo_branchExists___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_branchExists___closed__3;
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_revisionExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "^{commit}"};
static const lean_object* l_Lake_GitRepo_revisionExists___closed__0 = (const lean_object*)&l_Lake_GitRepo_revisionExists___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_revisionExists___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_revisionExists___closed__1;
static lean_once_cell_t l_Lake_GitRepo_revisionExists___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_revisionExists___closed__2;
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getTags___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tag"};
static const lean_object* l_Lake_GitRepo_getTags___closed__0 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__0_value;
static const lean_array_object l_Lake_GitRepo_getTags___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_GitRepo_getTags___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_getTags___closed__1 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "describe"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--exact-match"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "remote"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "get-url"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "diff"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__0 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value;
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "--exit-code"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__1 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value;
static const lean_array_object l_Lake_GitRepo_hasNoDiff___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value),((lean_object*)&l_Lake_GitRepo_getHeadRevision_x3f___closed__0_value),((lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__2 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__1(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_7_ = lean_string_utf8_byte_size(v___x_6_);
return v___x_7_;
}
}
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_10_ = lean_string_utf8_byte_size(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object* v_url_11_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_27_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_28_ = lean_string_utf8_byte_size(v_url_11_);
v___x_29_ = lean_obj_once(&l_Lake_Git_filterUrl_x3f___closed__3, &l_Lake_Git_filterUrl_x3f___closed__3_once, _init_l_Lake_Git_filterUrl_x3f___closed__3);
v___x_30_ = lean_nat_dec_le(v___x_29_, v___x_28_);
if (v___x_30_ == 0)
{
goto v___jp_12_;
}
else
{
lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_string_memcmp(v_url_11_, v___x_27_, v___x_31_, v___x_31_, v___x_29_);
if (v___x_32_ == 0)
{
goto v___jp_12_;
}
else
{
lean_object* v___x_33_; 
lean_dec_ref(v_url_11_);
v___x_33_ = lean_box(0);
return v___x_33_;
}
}
v___jp_12_:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_13_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_14_ = lean_string_utf8_byte_size(v_url_11_);
v___x_15_ = lean_obj_once(&l_Lake_Git_filterUrl_x3f___closed__1, &l_Lake_Git_filterUrl_x3f___closed__1_once, _init_l_Lake_Git_filterUrl_x3f___closed__1);
v___x_16_ = lean_nat_dec_le(v___x_15_, v___x_14_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; 
v___x_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_17_, 0, v_url_11_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_nat_sub(v___x_14_, v___x_15_);
v___x_20_ = lean_string_memcmp(v_url_11_, v___x_13_, v___x_19_, v___x_18_, v___x_15_);
lean_dec(v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_url_11_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_22_ = lean_unsigned_to_nat(4u);
lean_inc_ref(v_url_11_);
v___x_23_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_23_, 0, v_url_11_);
lean_ctor_set(v___x_23_, 1, v___x_18_);
lean_ctor_set(v___x_23_, 2, v___x_14_);
v___x_24_ = l_String_Slice_Pos_prevn(v___x_23_, v___x_14_, v___x_22_);
lean_dec_ref(v___x_23_);
v___x_25_ = lean_string_utf8_extract(v_url_11_, v___x_18_, v___x_24_);
lean_dec(v___x_24_);
lean_dec_ref(v_url_11_);
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Git_isFullObjectName_spec__0(lean_object* v_s_34_, lean_object* v_pos_35_){
_start:
{
lean_object* v_str_36_; lean_object* v_startInclusive_37_; lean_object* v_endExclusive_38_; lean_object* v___x_39_; uint8_t v___y_47_; lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
v_str_36_ = lean_ctor_get(v_s_34_, 0);
v_startInclusive_37_ = lean_ctor_get(v_s_34_, 1);
v_endExclusive_38_ = lean_ctor_get(v_s_34_, 2);
v___x_39_ = lean_nat_add(v_startInclusive_37_, v_pos_35_);
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = lean_nat_sub(v_endExclusive_38_, v___x_39_);
v___x_50_ = lean_nat_dec_eq(v___x_48_, v___x_49_);
lean_dec(v___x_49_);
if (v___x_50_ == 0)
{
uint32_t v___x_51_; uint8_t v___y_53_; uint32_t v___x_58_; uint8_t v___x_59_; 
v___x_51_ = lean_string_utf8_get_fast(v_str_36_, v___x_39_);
v___x_58_ = 48;
v___x_59_ = lean_uint32_dec_le(v___x_58_, v___x_51_);
if (v___x_59_ == 0)
{
v___y_53_ = v___x_59_;
goto v___jp_52_;
}
else
{
uint32_t v___x_60_; uint8_t v___x_61_; 
v___x_60_ = 57;
v___x_61_ = lean_uint32_dec_le(v___x_51_, v___x_60_);
v___y_53_ = v___x_61_;
goto v___jp_52_;
}
v___jp_52_:
{
if (v___y_53_ == 0)
{
uint32_t v___x_54_; uint8_t v___x_55_; 
v___x_54_ = 97;
v___x_55_ = lean_uint32_dec_le(v___x_54_, v___x_51_);
if (v___x_55_ == 0)
{
v___y_47_ = v___x_55_;
goto v___jp_46_;
}
else
{
uint32_t v___x_56_; uint8_t v___x_57_; 
v___x_56_ = 102;
v___x_57_ = lean_uint32_dec_le(v___x_51_, v___x_56_);
v___y_47_ = v___x_57_;
goto v___jp_46_;
}
}
else
{
goto v___jp_40_;
}
}
}
else
{
lean_dec(v___x_39_);
return v_pos_35_;
}
v___jp_40_:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_41_ = lean_string_utf8_next_fast(v_str_36_, v___x_39_);
v___x_42_ = lean_nat_sub(v___x_41_, v___x_39_);
lean_dec(v___x_39_);
v___x_43_ = lean_nat_add(v_pos_35_, v___x_42_);
lean_dec(v___x_42_);
v___x_44_ = l_String_instDecidableLtRaw___aux__1(v_pos_35_, v___x_43_);
if (v___x_44_ == 0)
{
lean_dec(v___x_43_);
return v_pos_35_;
}
else
{
lean_dec(v_pos_35_);
v_pos_35_ = v___x_43_;
goto _start;
}
}
v___jp_46_:
{
if (v___y_47_ == 0)
{
lean_dec(v___x_39_);
return v_pos_35_;
}
else
{
goto v___jp_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Git_isFullObjectName_spec__0___boxed(lean_object* v_s_62_, lean_object* v_pos_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_String_Slice_Pos_skipWhile___at___00Lake_Git_isFullObjectName_spec__0(v_s_62_, v_pos_63_);
lean_dec_ref(v_s_62_);
return v_res_64_;
}
}
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object* v_rev_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = lean_string_length(v_rev_65_);
v___x_67_ = lean_unsigned_to_nat(40u);
v___x_68_ = lean_nat_dec_eq(v___x_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_dec_ref(v_rev_65_);
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_string_utf8_byte_size(v_rev_65_);
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v_rev_65_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_70_);
v___x_72_ = l_String_Slice_Pos_skipWhile___at___00Lake_Git_isFullObjectName_spec__0(v___x_71_, v___x_69_);
lean_dec_ref(v___x_71_);
v___x_73_ = lean_nat_sub(v___x_70_, v___x_72_);
lean_dec(v___x_72_);
v___x_74_ = lean_nat_dec_eq(v___x_73_, v___x_69_);
lean_dec(v___x_73_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object* v_rev_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Lake_Git_isFullObjectName(v_rev_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0(lean_object* v_x_78_){
_start:
{
lean_inc_ref(v_x_78_);
return v_x_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0___boxed(lean_object* v_x_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lake_instCoeFilePathGitRepo___lam__0(v_x_79_);
lean_dec_ref(v_x_79_);
return v_res_80_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object* v_repo_86_){
_start:
{
uint8_t v___x_88_; 
v___x_88_ = l_System_FilePath_isDir(v_repo_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object* v_repo_89_, lean_object* v_a_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_Lake_GitRepo_dirExists(v_repo_89_);
lean_dec_ref(v_repo_89_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object* v_args_97_, lean_object* v_repo_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_101_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_102_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v_repo_98_);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_106_ = 1;
v___x_107_ = 0;
v___x_108_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_108_, 0, v___x_101_);
lean_ctor_set(v___x_108_, 1, v___x_102_);
lean_ctor_set(v___x_108_, 2, v_args_97_);
lean_ctor_set(v___x_108_, 3, v___x_103_);
lean_ctor_set(v___x_108_, 4, v___x_105_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*5, v___x_106_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*5 + 1, v___x_107_);
v___x_109_ = l_Lake_captureProc_x27(v___x_108_, v_a_99_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_126_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_a_111_ = lean_ctor_get(v___x_109_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_126_ == 0)
{
v___x_113_ = v___x_109_;
v_isShared_114_ = v_isSharedCheck_126_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_126_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_stdout_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_str_119_; lean_object* v_startInclusive_120_; lean_object* v_endExclusive_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v_stdout_115_ = lean_ctor_get(v_a_110_, 0);
lean_inc_ref(v_stdout_115_);
lean_dec(v_a_110_);
v___x_116_ = lean_string_utf8_byte_size(v_stdout_115_);
v___x_117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_117_, 0, v_stdout_115_);
lean_ctor_set(v___x_117_, 1, v___x_104_);
lean_ctor_set(v___x_117_, 2, v___x_116_);
v___x_118_ = l_String_Slice_trimAscii(v___x_117_);
v_str_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc_ref(v_str_119_);
v_startInclusive_120_ = lean_ctor_get(v___x_118_, 1);
lean_inc(v_startInclusive_120_);
v_endExclusive_121_ = lean_ctor_get(v___x_118_, 2);
lean_inc(v_endExclusive_121_);
lean_dec_ref(v___x_118_);
v___x_122_ = lean_string_utf8_extract(v_str_119_, v_startInclusive_120_, v_endExclusive_121_);
lean_dec(v_endExclusive_121_);
lean_dec(v_startInclusive_120_);
lean_dec_ref(v_str_119_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_122_);
v___x_124_ = v___x_113_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_a_111_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
else
{
lean_object* v_a_127_; lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
v_a_127_ = lean_ctor_get(v___x_109_, 0);
v_a_128_ = lean_ctor_get(v___x_109_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_135_ == 0)
{
v___x_130_ = v___x_109_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_inc(v_a_127_);
lean_dec(v___x_109_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_127_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_a_128_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object* v_args_136_, lean_object* v_repo_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lake_GitRepo_captureGit(v_args_136_, v_repo_137_, v_a_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object* v_args_141_, lean_object* v_repo_142_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_144_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_145_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_146_, 0, v_repo_142_);
v___x_147_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_148_ = 1;
v___x_149_ = 0;
v___x_150_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_150_, 0, v___x_144_);
lean_ctor_set(v___x_150_, 1, v___x_145_);
lean_ctor_set(v___x_150_, 2, v_args_141_);
lean_ctor_set(v___x_150_, 3, v___x_146_);
lean_ctor_set(v___x_150_, 4, v___x_147_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*5, v___x_148_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*5 + 1, v___x_149_);
v___x_151_ = l_Lake_captureProc_x3f(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object* v_args_152_, lean_object* v_repo_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lake_GitRepo_captureGit_x3f(v_args_152_, v_repo_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object* v_args_156_, lean_object* v_repo_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_160_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_161_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_162_, 0, v_repo_157_);
v___x_163_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_164_ = 1;
v___x_165_ = 0;
v___x_166_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_166_, 0, v___x_160_);
lean_ctor_set(v___x_166_, 1, v___x_161_);
lean_ctor_set(v___x_166_, 2, v_args_156_);
lean_ctor_set(v___x_166_, 3, v___x_162_);
lean_ctor_set(v___x_166_, 4, v___x_163_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*5, v___x_164_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*5 + 1, v___x_165_);
v___x_167_ = l_Lake_proc(v___x_166_, v___x_164_, v_a_158_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object* v_args_168_, lean_object* v_repo_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lake_GitRepo_execGit(v_args_168_, v_repo_169_, v_a_170_);
return v_res_172_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object* v_args_173_, lean_object* v_repo_174_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_176_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_177_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_178_, 0, v_repo_174_);
v___x_179_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_180_ = 1;
v___x_181_ = 0;
v___x_182_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_182_, 0, v___x_176_);
lean_ctor_set(v___x_182_, 1, v___x_177_);
lean_ctor_set(v___x_182_, 2, v_args_173_);
lean_ctor_set(v___x_182_, 3, v___x_178_);
lean_ctor_set(v___x_182_, 4, v___x_179_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*5, v___x_180_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*5 + 1, v___x_181_);
v___x_183_ = l_Lake_testProc(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object* v_args_184_, lean_object* v_repo_185_, lean_object* v_a_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = l_Lake_GitRepo_testGit(v_args_184_, v_repo_185_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__1(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_190_ = ((lean_object*)(l_Lake_GitRepo_clone___closed__0));
v___x_191_ = lean_unsigned_to_nat(3u);
v___x_192_ = lean_mk_empty_array_with_capacity(v___x_191_);
v___x_193_ = lean_array_push(v___x_192_, v___x_190_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object* v_url_194_, lean_object* v_repo_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_198_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_199_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_200_ = lean_obj_once(&l_Lake_GitRepo_clone___closed__1, &l_Lake_GitRepo_clone___closed__1_once, _init_l_Lake_GitRepo_clone___closed__1);
v___x_201_ = lean_array_push(v___x_200_, v_url_194_);
v___x_202_ = lean_array_push(v___x_201_, v_repo_195_);
v___x_203_ = lean_box(0);
v___x_204_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_205_ = 1;
v___x_206_ = 0;
v___x_207_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_207_, 0, v___x_198_);
lean_ctor_set(v___x_207_, 1, v___x_199_);
lean_ctor_set(v___x_207_, 2, v___x_202_);
lean_ctor_set(v___x_207_, 3, v___x_203_);
lean_ctor_set(v___x_207_, 4, v___x_204_);
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*5, v___x_205_);
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*5 + 1, v___x_206_);
v___x_208_ = l_Lake_proc(v___x_207_, v___x_205_, v_a_196_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object* v_url_209_, lean_object* v_repo_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lake_GitRepo_clone(v_url_209_, v_repo_210_, v_a_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object* v_repo_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_225_ = ((lean_object*)(l_Lake_GitRepo_quietInit___closed__2));
v___x_226_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_227_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v_repo_222_);
v___x_229_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_230_ = 1;
v___x_231_ = 0;
v___x_232_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_232_, 0, v___x_226_);
lean_ctor_set(v___x_232_, 1, v___x_227_);
lean_ctor_set(v___x_232_, 2, v___x_225_);
lean_ctor_set(v___x_232_, 3, v___x_228_);
lean_ctor_set(v___x_232_, 4, v___x_229_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*5, v___x_230_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*5 + 1, v___x_231_);
v___x_233_ = l_Lake_proc(v___x_232_, v___x_230_, v_a_223_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object* v_repo_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lake_GitRepo_quietInit(v_repo_234_, v_a_235_);
return v_res_237_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object* v_repo_246_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_248_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__2));
v___x_249_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_250_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v_repo_246_);
v___x_252_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_253_ = 1;
v___x_254_ = 0;
v___x_255_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_255_, 0, v___x_249_);
lean_ctor_set(v___x_255_, 1, v___x_250_);
lean_ctor_set(v___x_255_, 2, v___x_248_);
lean_ctor_set(v___x_255_, 3, v___x_251_);
lean_ctor_set(v___x_255_, 4, v___x_252_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*5, v___x_253_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*5 + 1, v___x_254_);
v___x_256_ = l_Lake_testProc(v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object* v_repo_257_, lean_object* v_a_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Lake_GitRepo_insideWorkTree(v_repo_257_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__3(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_264_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__0));
v___x_265_ = lean_unsigned_to_nat(4u);
v___x_266_ = lean_mk_empty_array_with_capacity(v___x_265_);
v___x_267_ = lean_array_push(v___x_266_, v___x_264_);
return v___x_267_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__4(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_269_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__3, &l_Lake_GitRepo_fetch___closed__3_once, _init_l_Lake_GitRepo_fetch___closed__3);
v___x_270_ = lean_array_push(v___x_269_, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__5(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__2));
v___x_272_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__4, &l_Lake_GitRepo_fetch___closed__4_once, _init_l_Lake_GitRepo_fetch___closed__4);
v___x_273_ = lean_array_push(v___x_272_, v___x_271_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object* v_repo_274_, lean_object* v_remote_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_278_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__5, &l_Lake_GitRepo_fetch___closed__5_once, _init_l_Lake_GitRepo_fetch___closed__5);
v___x_279_ = lean_array_push(v___x_278_, v_remote_275_);
v___x_280_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_281_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v_repo_274_);
v___x_283_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_284_ = 1;
v___x_285_ = 0;
v___x_286_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_286_, 0, v___x_280_);
lean_ctor_set(v___x_286_, 1, v___x_281_);
lean_ctor_set(v___x_286_, 2, v___x_279_);
lean_ctor_set(v___x_286_, 3, v___x_282_);
lean_ctor_set(v___x_286_, 4, v___x_283_);
lean_ctor_set_uint8(v___x_286_, sizeof(void*)*5, v___x_284_);
lean_ctor_set_uint8(v___x_286_, sizeof(void*)*5 + 1, v___x_285_);
v___x_287_ = l_Lake_proc(v___x_286_, v___x_284_, v_a_276_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object* v_repo_288_, lean_object* v_remote_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lake_GitRepo_fetch(v_repo_288_, v_remote_289_, v_a_290_);
return v_res_292_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__2(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_295_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_296_ = lean_unsigned_to_nat(3u);
v___x_297_ = lean_mk_empty_array_with_capacity(v___x_296_);
v___x_298_ = lean_array_push(v___x_297_, v___x_295_);
return v___x_298_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__3(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__1));
v___x_300_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__2, &l_Lake_GitRepo_checkoutBranch___closed__2_once, _init_l_Lake_GitRepo_checkoutBranch___closed__2);
v___x_301_ = lean_array_push(v___x_300_, v___x_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object* v_branch_302_, lean_object* v_repo_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_306_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__3, &l_Lake_GitRepo_checkoutBranch___closed__3_once, _init_l_Lake_GitRepo_checkoutBranch___closed__3);
v___x_307_ = lean_array_push(v___x_306_, v_branch_302_);
v___x_308_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_309_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v_repo_303_);
v___x_311_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_312_ = 1;
v___x_313_ = 0;
v___x_314_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_314_, 0, v___x_308_);
lean_ctor_set(v___x_314_, 1, v___x_309_);
lean_ctor_set(v___x_314_, 2, v___x_307_);
lean_ctor_set(v___x_314_, 3, v___x_310_);
lean_ctor_set(v___x_314_, 4, v___x_311_);
lean_ctor_set_uint8(v___x_314_, sizeof(void*)*5, v___x_312_);
lean_ctor_set_uint8(v___x_314_, sizeof(void*)*5 + 1, v___x_313_);
v___x_315_ = l_Lake_proc(v___x_314_, v___x_312_, v_a_304_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object* v_branch_316_, lean_object* v_repo_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lake_GitRepo_checkoutBranch(v_branch_316_, v_repo_317_, v_a_318_);
return v_res_320_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__2(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_323_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_324_ = lean_unsigned_to_nat(4u);
v___x_325_ = lean_mk_empty_array_with_capacity(v___x_324_);
v___x_326_ = lean_array_push(v___x_325_, v___x_323_);
return v___x_326_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__3(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = ((lean_object*)(l_Lake_GitRepo_checkoutDetach___closed__0));
v___x_328_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__2, &l_Lake_GitRepo_checkoutDetach___closed__2_once, _init_l_Lake_GitRepo_checkoutDetach___closed__2);
v___x_329_ = lean_array_push(v___x_328_, v___x_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object* v_hash_330_, lean_object* v_repo_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_334_ = ((lean_object*)(l_Lake_GitRepo_checkoutDetach___closed__1));
v___x_335_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__3, &l_Lake_GitRepo_checkoutDetach___closed__3_once, _init_l_Lake_GitRepo_checkoutDetach___closed__3);
v___x_336_ = lean_array_push(v___x_335_, v_hash_330_);
v___x_337_ = lean_array_push(v___x_336_, v___x_334_);
v___x_338_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_339_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_340_, 0, v_repo_331_);
v___x_341_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_342_ = 1;
v___x_343_ = 0;
v___x_344_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_344_, 0, v___x_338_);
lean_ctor_set(v___x_344_, 1, v___x_339_);
lean_ctor_set(v___x_344_, 2, v___x_337_);
lean_ctor_set(v___x_344_, 3, v___x_340_);
lean_ctor_set(v___x_344_, 4, v___x_341_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*5, v___x_342_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*5 + 1, v___x_343_);
v___x_345_ = l_Lake_proc(v___x_344_, v___x_342_, v_a_332_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object* v_hash_346_, lean_object* v_repo_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lake_GitRepo_checkoutDetach(v_hash_346_, v_repo_347_, v_a_348_);
return v_res_350_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_353_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_354_ = lean_unsigned_to_nat(4u);
v___x_355_ = lean_mk_empty_array_with_capacity(v___x_354_);
v___x_356_ = lean_array_push(v___x_355_, v___x_353_);
return v___x_356_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_358_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__2, &l_Lake_GitRepo_resolveRevision_x3f___closed__2_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2);
v___x_359_ = lean_array_push(v___x_358_, v___x_357_);
return v___x_359_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__1));
v___x_361_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__3, &l_Lake_GitRepo_resolveRevision_x3f___closed__3_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3);
v___x_362_ = lean_array_push(v___x_361_, v___x_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object* v_rev_363_, lean_object* v_repo_364_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_366_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__4, &l_Lake_GitRepo_resolveRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4);
v___x_367_ = lean_array_push(v___x_366_, v_rev_363_);
v___x_368_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_369_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v_repo_364_);
v___x_371_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_372_ = 1;
v___x_373_ = 0;
v___x_374_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_374_, 0, v___x_368_);
lean_ctor_set(v___x_374_, 1, v___x_369_);
lean_ctor_set(v___x_374_, 2, v___x_367_);
lean_ctor_set(v___x_374_, 3, v___x_370_);
lean_ctor_set(v___x_374_, 4, v___x_371_);
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*5, v___x_372_);
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*5 + 1, v___x_373_);
v___x_375_ = l_Lake_captureProc_x3f(v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object* v_rev_376_, lean_object* v_repo_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_376_, v_repo_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object* v_rev_382_, lean_object* v_repo_383_, lean_object* v_a_384_){
_start:
{
uint8_t v___x_386_; 
lean_inc_ref(v_rev_382_);
v___x_386_ = l_Lake_Git_isFullObjectName(v_rev_382_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
lean_inc_ref(v_repo_383_);
lean_inc_ref(v_rev_382_);
v___x_387_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_382_, v_repo_383_);
if (lean_obj_tag(v___x_387_) == 1)
{
lean_object* v_val_388_; lean_object* v___x_389_; 
lean_dec_ref(v_repo_383_);
lean_dec_ref(v_rev_382_);
v_val_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_val_388_);
lean_dec_ref(v___x_387_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_val_388_);
lean_ctor_set(v___x_389_, 1, v_a_384_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec(v___x_387_);
v___x_390_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_391_ = lean_string_append(v_repo_383_, v___x_390_);
v___x_392_ = lean_string_append(v___x_391_, v_rev_382_);
lean_dec_ref(v_rev_382_);
v___x_393_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_394_ = lean_string_append(v___x_392_, v___x_393_);
v___x_395_ = 3;
v___x_396_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*1, v___x_395_);
v___x_397_ = lean_array_get_size(v_a_384_);
v___x_398_ = lean_array_push(v_a_384_, v___x_396_);
v___x_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
return v___x_399_;
}
}
else
{
lean_object* v___x_400_; 
lean_dec_ref(v_repo_383_);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_rev_382_);
lean_ctor_set(v___x_400_, 1, v_a_384_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object* v_rev_401_, lean_object* v_repo_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lake_GitRepo_resolveRevision(v_rev_401_, v_repo_402_, v_a_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object* v_repo_407_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision_x3f___closed__0));
v___x_410_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_409_, v_repo_407_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object* v_repo_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lake_GitRepo_getHeadRevision_x3f(v_repo_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object* v_repo_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision_x3f___closed__0));
lean_inc_ref(v_repo_415_);
v___x_419_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_418_, v_repo_415_);
if (lean_obj_tag(v___x_419_) == 1)
{
lean_object* v_val_420_; lean_object* v___x_421_; 
lean_dec_ref(v_repo_415_);
v_val_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_val_420_);
lean_dec_ref(v___x_419_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_val_420_);
lean_ctor_set(v___x_421_, 1, v_a_416_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec(v___x_419_);
v___x_422_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision___closed__0));
v___x_423_ = lean_string_append(v_repo_415_, v___x_422_);
v___x_424_ = 3;
v___x_425_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*1, v___x_424_);
v___x_426_ = lean_array_get_size(v_a_416_);
v___x_427_ = lean_array_push(v_a_416_, v___x_425_);
v___x_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object* v_repo_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lake_GitRepo_getHeadRevision(v_repo_429_, v_a_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object* v_s_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0));
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object* v_s_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v_s_437_);
lean_dec_ref(v_s_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v___x_441_, lean_object* v_a_442_, lean_object* v_b_443_){
_start:
{
lean_object* v_it_445_; lean_object* v_startInclusive_446_; lean_object* v_endExclusive_447_; 
if (lean_obj_tag(v_a_442_) == 0)
{
lean_object* v_currPos_452_; lean_object* v_searcher_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_479_; 
v_currPos_452_ = lean_ctor_get(v_a_442_, 0);
v_searcher_453_ = lean_ctor_get(v_a_442_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_a_442_);
if (v_isSharedCheck_479_ == 0)
{
v___x_455_ = v_a_442_;
v_isShared_456_ = v_isSharedCheck_479_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_searcher_453_);
lean_inc(v_currPos_452_);
lean_dec(v_a_442_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_479_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v_startInclusive_457_; lean_object* v_endExclusive_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_startInclusive_457_ = lean_ctor_get(v___x_440_, 1);
v_endExclusive_458_ = lean_ctor_get(v___x_440_, 2);
v___x_459_ = lean_nat_sub(v_endExclusive_458_, v_startInclusive_457_);
v___x_460_ = lean_nat_dec_eq(v_searcher_453_, v___x_459_);
lean_dec(v___x_459_);
if (v___x_460_ == 0)
{
uint32_t v___x_461_; uint32_t v___x_462_; uint8_t v___x_463_; 
v___x_461_ = 10;
v___x_462_ = lean_string_utf8_get_fast(v___x_439_, v_searcher_453_);
v___x_463_ = lean_uint32_dec_eq(v___x_462_, v___x_461_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_string_utf8_next_fast(v___x_439_, v_searcher_453_);
lean_dec(v_searcher_453_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_464_);
v___x_466_ = v___x_455_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_currPos_452_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_464_);
v___x_466_ = v_reuseFailAlloc_468_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
v_a_442_ = v___x_466_;
goto _start;
}
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_slice_472_; lean_object* v_nextIt_474_; 
v___x_469_ = lean_string_utf8_next_fast(v___x_439_, v_searcher_453_);
v___x_470_ = lean_nat_sub(v___x_469_, v_searcher_453_);
v___x_471_ = lean_nat_add(v_searcher_453_, v___x_470_);
lean_dec(v___x_470_);
v_slice_472_ = l_String_Slice_subslice_x21(v___x_440_, v_currPos_452_, v_searcher_453_);
lean_inc(v___x_471_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_471_);
lean_ctor_set(v___x_455_, 0, v___x_471_);
v_nextIt_474_ = v___x_455_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_471_);
v_nextIt_474_ = v_reuseFailAlloc_477_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v_startInclusive_475_; lean_object* v_endExclusive_476_; 
v_startInclusive_475_ = lean_ctor_get(v_slice_472_, 0);
lean_inc(v_startInclusive_475_);
v_endExclusive_476_ = lean_ctor_get(v_slice_472_, 1);
lean_inc(v_endExclusive_476_);
lean_dec_ref(v_slice_472_);
v_it_445_ = v_nextIt_474_;
v_startInclusive_446_ = v_startInclusive_475_;
v_endExclusive_447_ = v_endExclusive_476_;
goto v___jp_444_;
}
}
}
else
{
lean_object* v___x_478_; 
lean_del_object(v___x_455_);
lean_dec(v_searcher_453_);
v___x_478_ = lean_box(1);
lean_inc(v___x_441_);
v_it_445_ = v___x_478_;
v_startInclusive_446_ = v_currPos_452_;
v_endExclusive_447_ = v___x_441_;
goto v___jp_444_;
}
}
}
else
{
lean_dec(v___x_441_);
lean_dec_ref(v___x_439_);
return v_b_443_;
}
v___jp_444_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
lean_inc_ref(v___x_439_);
v___x_448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_448_, 0, v___x_439_);
lean_ctor_set(v___x_448_, 1, v_startInclusive_446_);
lean_ctor_set(v___x_448_, 2, v_endExclusive_447_);
v___x_449_ = l_String_Slice_toString(v___x_448_);
lean_dec_ref(v___x_448_);
v___x_450_ = lean_array_push(v_b_443_, v___x_449_);
v_a_442_ = v_it_445_;
v_b_443_ = v___x_450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object* v___x_480_, lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v_a_483_, lean_object* v_b_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_480_, v___x_481_, v___x_482_, v_a_483_, v_b_484_);
lean_dec_ref(v___x_481_);
return v_res_485_;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevisions___closed__3(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_494_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__2));
v___x_495_ = lean_unsigned_to_nat(2u);
v___x_496_ = lean_mk_empty_array_with_capacity(v___x_495_);
v___x_497_ = lean_array_push(v___x_496_, v___x_494_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object* v_repo_498_, lean_object* v_n_499_, lean_object* v_a_500_){
_start:
{
lean_object* v___y_503_; lean_object* v_args_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_args_549_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__1));
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = lean_nat_dec_eq(v_n_499_, v___x_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_552_ = l_Nat_reprFast(v_n_499_);
v___x_553_ = lean_obj_once(&l_Lake_GitRepo_getHeadRevisions___closed__3, &l_Lake_GitRepo_getHeadRevisions___closed__3_once, _init_l_Lake_GitRepo_getHeadRevisions___closed__3);
v___x_554_ = lean_array_push(v___x_553_, v___x_552_);
v___x_555_ = l_Array_append___redArg(v_args_549_, v___x_554_);
lean_dec_ref(v___x_554_);
v___y_503_ = v___x_555_;
goto v___jp_502_;
}
else
{
lean_dec(v_n_499_);
v___y_503_ = v_args_549_;
goto v___jp_502_;
}
v___jp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_504_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_505_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v_repo_498_);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_509_ = 1;
v___x_510_ = 0;
v___x_511_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_511_, 0, v___x_504_);
lean_ctor_set(v___x_511_, 1, v___x_505_);
lean_ctor_set(v___x_511_, 2, v___y_503_);
lean_ctor_set(v___x_511_, 3, v___x_506_);
lean_ctor_set(v___x_511_, 4, v___x_508_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*5, v___x_509_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*5 + 1, v___x_510_);
v___x_512_ = l_Lake_captureProc_x27(v___x_511_, v_a_500_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_539_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
v_a_514_ = lean_ctor_get(v___x_512_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_539_ == 0)
{
v___x_516_ = v___x_512_;
v_isShared_517_ = v_isSharedCheck_539_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_inc(v_a_513_);
lean_dec(v___x_512_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_539_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_stdout_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_str_522_; lean_object* v_startInclusive_523_; lean_object* v_endExclusive_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_538_; 
v_stdout_518_ = lean_ctor_get(v_a_513_, 0);
lean_inc_ref(v_stdout_518_);
lean_dec(v_a_513_);
v___x_519_ = lean_string_utf8_byte_size(v_stdout_518_);
v___x_520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_520_, 0, v_stdout_518_);
lean_ctor_set(v___x_520_, 1, v___x_507_);
lean_ctor_set(v___x_520_, 2, v___x_519_);
v___x_521_ = l_String_Slice_trimAscii(v___x_520_);
v_str_522_ = lean_ctor_get(v___x_521_, 0);
v_startInclusive_523_ = lean_ctor_get(v___x_521_, 1);
v_endExclusive_524_ = lean_ctor_get(v___x_521_, 2);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_538_ == 0)
{
v___x_526_ = v___x_521_;
v_isShared_527_ = v_isSharedCheck_538_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_endExclusive_524_);
lean_inc(v_startInclusive_523_);
lean_inc(v_str_522_);
lean_dec(v___x_521_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_538_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_528_ = lean_string_utf8_extract(v_str_522_, v_startInclusive_523_, v_endExclusive_524_);
lean_dec(v_endExclusive_524_);
lean_dec(v_startInclusive_523_);
lean_dec_ref(v_str_522_);
v___x_529_ = lean_string_utf8_byte_size(v___x_528_);
lean_inc_ref(v___x_528_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 2, v___x_529_);
lean_ctor_set(v___x_526_, 1, v___x_507_);
lean_ctor_set(v___x_526_, 0, v___x_528_);
v___x_531_ = v___x_526_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_537_, 2, v___x_529_);
v___x_531_ = v_reuseFailAlloc_537_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_532_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v___x_531_);
v___x_533_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_528_, v___x_531_, v___x_529_, v___x_532_, v___x_508_);
lean_dec_ref(v___x_531_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_533_);
v___x_535_ = v___x_516_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_a_514_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_a_540_ = lean_ctor_get(v___x_512_, 0);
v_a_541_ = lean_ctor_get(v___x_512_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_512_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_inc(v_a_540_);
lean_dec(v___x_512_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_540_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object* v_repo_556_, lean_object* v_n_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lake_GitRepo_getHeadRevisions(v_repo_556_, v_n_557_, v_a_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object* v___x_561_, lean_object* v___x_562_, lean_object* v___x_563_, lean_object* v_inst_564_, lean_object* v_R_565_, lean_object* v_a_566_, lean_object* v_b_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_561_, v___x_562_, v___x_563_, v_a_566_, v_b_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object* v___x_569_, lean_object* v___x_570_, lean_object* v___x_571_, lean_object* v_inst_572_, lean_object* v_R_573_, lean_object* v_a_574_, lean_object* v_b_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(v___x_569_, v___x_570_, v___x_571_, v_inst_572_, v_R_573_, v_a_574_, v_b_575_);
lean_dec_ref(v___x_570_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object* v_rev_578_, lean_object* v_remote_579_, lean_object* v_repo_580_, lean_object* v_a_581_){
_start:
{
uint8_t v___x_583_; 
lean_inc_ref(v_rev_578_);
v___x_583_ = l_Lake_Git_isFullObjectName(v_rev_578_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_584_ = ((lean_object*)(l_Lake_GitRepo_resolveRemoteRevision___closed__0));
v___x_585_ = lean_string_append(v_remote_579_, v___x_584_);
v___x_586_ = lean_string_append(v___x_585_, v_rev_578_);
lean_inc_ref(v_repo_580_);
v___x_587_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_586_, v_repo_580_);
if (lean_obj_tag(v___x_587_) == 1)
{
lean_object* v_val_588_; lean_object* v___x_589_; 
lean_dec_ref(v_repo_580_);
lean_dec_ref(v_rev_578_);
v_val_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_val_588_);
lean_dec_ref(v___x_587_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v_val_588_);
lean_ctor_set(v___x_589_, 1, v_a_581_);
return v___x_589_;
}
else
{
lean_object* v___x_590_; 
lean_dec(v___x_587_);
lean_inc_ref(v_repo_580_);
lean_inc_ref(v_rev_578_);
v___x_590_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_578_, v_repo_580_);
if (lean_obj_tag(v___x_590_) == 1)
{
lean_object* v_val_591_; lean_object* v___x_592_; 
lean_dec_ref(v_repo_580_);
lean_dec_ref(v_rev_578_);
v_val_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_val_591_);
lean_dec_ref(v___x_590_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v_val_591_);
lean_ctor_set(v___x_592_, 1, v_a_581_);
return v___x_592_;
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v___x_590_);
v___x_593_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_594_ = lean_string_append(v_repo_580_, v___x_593_);
v___x_595_ = lean_string_append(v___x_594_, v_rev_578_);
lean_dec_ref(v_rev_578_);
v___x_596_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_597_ = lean_string_append(v___x_595_, v___x_596_);
v___x_598_ = 3;
v___x_599_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*1, v___x_598_);
v___x_600_ = lean_array_get_size(v_a_581_);
v___x_601_ = lean_array_push(v_a_581_, v___x_599_);
v___x_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
return v___x_602_;
}
}
}
else
{
lean_object* v___x_603_; 
lean_dec_ref(v_repo_580_);
lean_dec_ref(v_remote_579_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v_rev_578_);
lean_ctor_set(v___x_603_, 1, v_a_581_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object* v_rev_604_, lean_object* v_remote_605_, lean_object* v_repo_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lake_GitRepo_resolveRemoteRevision(v_rev_604_, v_remote_605_, v_repo_606_, v_a_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object* v_repo_610_, lean_object* v_rev_x3f_611_, lean_object* v_remote_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___x_615_; 
lean_inc_ref(v_remote_612_);
lean_inc_ref(v_repo_610_);
v___x_615_ = l_Lake_GitRepo_fetch(v_repo_610_, v_remote_612_, v_a_613_);
if (lean_obj_tag(v___x_615_) == 0)
{
if (lean_obj_tag(v_rev_x3f_611_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_a_616_ = lean_ctor_get(v___x_615_, 1);
lean_inc(v_a_616_);
lean_dec_ref(v___x_615_);
v___x_617_ = ((lean_object*)(l_Lake_Git_upstreamBranch___closed__0));
v___x_618_ = l_Lake_GitRepo_resolveRemoteRevision(v___x_617_, v_remote_612_, v_repo_610_, v_a_616_);
return v___x_618_;
}
else
{
lean_object* v_a_619_; lean_object* v_val_620_; lean_object* v___x_621_; 
v_a_619_ = lean_ctor_get(v___x_615_, 1);
lean_inc(v_a_619_);
lean_dec_ref(v___x_615_);
v_val_620_ = lean_ctor_get(v_rev_x3f_611_, 0);
lean_inc(v_val_620_);
lean_dec_ref(v_rev_x3f_611_);
v___x_621_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_620_, v_remote_612_, v_repo_610_, v_a_619_);
return v___x_621_;
}
}
else
{
lean_object* v_a_622_; lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v_remote_612_);
lean_dec(v_rev_x3f_611_);
lean_dec_ref(v_repo_610_);
v_a_622_ = lean_ctor_get(v___x_615_, 0);
v_a_623_ = lean_ctor_get(v___x_615_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_615_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_inc(v_a_622_);
lean_dec(v___x_615_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_622_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object* v_repo_631_, lean_object* v_rev_x3f_632_, lean_object* v_remote_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lake_GitRepo_findRemoteRevision(v_repo_631_, v_rev_x3f_632_, v_remote_633_, v_a_634_);
return v_res_636_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__2(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_639_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__0));
v___x_640_ = lean_unsigned_to_nat(3u);
v___x_641_ = lean_mk_empty_array_with_capacity(v___x_640_);
v___x_642_ = lean_array_push(v___x_641_, v___x_639_);
return v___x_642_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__3(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_644_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__2, &l_Lake_GitRepo_branchExists___closed__2_once, _init_l_Lake_GitRepo_branchExists___closed__2);
v___x_645_ = lean_array_push(v___x_644_, v___x_643_);
return v___x_645_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object* v_rev_646_, lean_object* v_repo_647_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_649_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__1));
v___x_650_ = lean_string_append(v___x_649_, v_rev_646_);
v___x_651_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__3, &l_Lake_GitRepo_branchExists___closed__3_once, _init_l_Lake_GitRepo_branchExists___closed__3);
v___x_652_ = lean_array_push(v___x_651_, v___x_650_);
v___x_653_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_654_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v_repo_647_);
v___x_656_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_657_ = 1;
v___x_658_ = 0;
v___x_659_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_659_, 0, v___x_653_);
lean_ctor_set(v___x_659_, 1, v___x_654_);
lean_ctor_set(v___x_659_, 2, v___x_652_);
lean_ctor_set(v___x_659_, 3, v___x_655_);
lean_ctor_set(v___x_659_, 4, v___x_656_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*5, v___x_657_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*5 + 1, v___x_658_);
v___x_660_ = l_Lake_testProc(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object* v_rev_661_, lean_object* v_repo_662_, lean_object* v_a_663_){
_start:
{
uint8_t v_res_664_; lean_object* v_r_665_; 
v_res_664_ = l_Lake_GitRepo_branchExists(v_rev_661_, v_repo_662_);
lean_dec_ref(v_rev_661_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__1(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_667_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_668_ = lean_unsigned_to_nat(3u);
v___x_669_ = lean_mk_empty_array_with_capacity(v___x_668_);
v___x_670_ = lean_array_push(v___x_669_, v___x_667_);
return v___x_670_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__2(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_672_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__1, &l_Lake_GitRepo_revisionExists___closed__1_once, _init_l_Lake_GitRepo_revisionExists___closed__1);
v___x_673_ = lean_array_push(v___x_672_, v___x_671_);
return v___x_673_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object* v_rev_674_, lean_object* v_repo_675_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; uint8_t v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_677_ = ((lean_object*)(l_Lake_GitRepo_revisionExists___closed__0));
v___x_678_ = lean_string_append(v_rev_674_, v___x_677_);
v___x_679_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__2, &l_Lake_GitRepo_revisionExists___closed__2_once, _init_l_Lake_GitRepo_revisionExists___closed__2);
v___x_680_ = lean_array_push(v___x_679_, v___x_678_);
v___x_681_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_682_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_683_, 0, v_repo_675_);
v___x_684_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_685_ = 1;
v___x_686_ = 0;
v___x_687_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_687_, 0, v___x_681_);
lean_ctor_set(v___x_687_, 1, v___x_682_);
lean_ctor_set(v___x_687_, 2, v___x_680_);
lean_ctor_set(v___x_687_, 3, v___x_683_);
lean_ctor_set(v___x_687_, 4, v___x_684_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*5, v___x_685_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*5 + 1, v___x_686_);
v___x_688_ = l_Lake_testProc(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object* v_rev_689_, lean_object* v_repo_690_, lean_object* v_a_691_){
_start:
{
uint8_t v_res_692_; lean_object* v_r_693_; 
v_res_692_ = l_Lake_GitRepo_revisionExists(v_rev_689_, v_repo_690_);
v_r_693_ = lean_box(v_res_692_);
return v_r_693_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object* v_repo_699_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; uint8_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_701_ = ((lean_object*)(l_Lake_GitRepo_getTags___closed__1));
v___x_702_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_703_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_704_, 0, v_repo_699_);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_707_ = 1;
v___x_708_ = 0;
v___x_709_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_709_, 0, v___x_702_);
lean_ctor_set(v___x_709_, 1, v___x_703_);
lean_ctor_set(v___x_709_, 2, v___x_701_);
lean_ctor_set(v___x_709_, 3, v___x_704_);
lean_ctor_set(v___x_709_, 4, v___x_706_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*5, v___x_707_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*5 + 1, v___x_708_);
v___x_710_ = l_Lake_captureProc_x3f(v___x_709_);
if (lean_obj_tag(v___x_710_) == 1)
{
lean_object* v_val_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_val_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_val_711_);
lean_dec_ref(v___x_710_);
v___x_712_ = lean_string_utf8_byte_size(v_val_711_);
lean_inc(v_val_711_);
v___x_713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_713_, 0, v_val_711_);
lean_ctor_set(v___x_713_, 1, v___x_705_);
lean_ctor_set(v___x_713_, 2, v___x_712_);
v___x_714_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v___x_713_);
v___x_715_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v_val_711_, v___x_713_, v___x_712_, v___x_714_, v___x_706_);
lean_dec_ref(v___x_713_);
v___x_716_ = lean_array_to_list(v___x_715_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; 
lean_dec(v___x_710_);
v___x_717_ = lean_box(0);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object* v_repo_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lake_GitRepo_getTags(v_repo_718_);
return v_res_720_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__2(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_723_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__0));
v___x_724_ = lean_unsigned_to_nat(4u);
v___x_725_ = lean_mk_empty_array_with_capacity(v___x_724_);
v___x_726_ = lean_array_push(v___x_725_, v___x_723_);
return v___x_726_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__3(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_728_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__2, &l_Lake_GitRepo_findTag_x3f___closed__2_once, _init_l_Lake_GitRepo_findTag_x3f___closed__2);
v___x_729_ = lean_array_push(v___x_728_, v___x_727_);
return v___x_729_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__4(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__1));
v___x_731_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__3, &l_Lake_GitRepo_findTag_x3f___closed__3_once, _init_l_Lake_GitRepo_findTag_x3f___closed__3);
v___x_732_ = lean_array_push(v___x_731_, v___x_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object* v_rev_733_, lean_object* v_repo_734_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_736_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__4, &l_Lake_GitRepo_findTag_x3f___closed__4_once, _init_l_Lake_GitRepo_findTag_x3f___closed__4);
v___x_737_ = lean_array_push(v___x_736_, v_rev_733_);
v___x_738_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_739_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_740_, 0, v_repo_734_);
v___x_741_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_742_ = 1;
v___x_743_ = 0;
v___x_744_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_744_, 0, v___x_738_);
lean_ctor_set(v___x_744_, 1, v___x_739_);
lean_ctor_set(v___x_744_, 2, v___x_737_);
lean_ctor_set(v___x_744_, 3, v___x_740_);
lean_ctor_set(v___x_744_, 4, v___x_741_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*5, v___x_742_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*5 + 1, v___x_743_);
v___x_745_ = l_Lake_captureProc_x3f(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object* v_rev_746_, lean_object* v_repo_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lake_GitRepo_findTag_x3f(v_rev_746_, v_repo_747_);
return v_res_749_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_752_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
v___x_753_ = lean_unsigned_to_nat(3u);
v___x_754_ = lean_mk_empty_array_with_capacity(v___x_753_);
v___x_755_ = lean_array_push(v___x_754_, v___x_752_);
return v___x_755_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__1));
v___x_757_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__2, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
v___x_758_ = lean_array_push(v___x_757_, v___x_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object* v_remote_759_, lean_object* v_repo_760_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; uint8_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_762_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__3, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3);
v___x_763_ = lean_array_push(v___x_762_, v_remote_759_);
v___x_764_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_765_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v_repo_760_);
v___x_767_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_768_ = 1;
v___x_769_ = 0;
v___x_770_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_770_, 0, v___x_764_);
lean_ctor_set(v___x_770_, 1, v___x_765_);
lean_ctor_set(v___x_770_, 2, v___x_763_);
lean_ctor_set(v___x_770_, 3, v___x_766_);
lean_ctor_set(v___x_770_, 4, v___x_767_);
lean_ctor_set_uint8(v___x_770_, sizeof(void*)*5, v___x_768_);
lean_ctor_set_uint8(v___x_770_, sizeof(void*)*5 + 1, v___x_769_);
v___x_771_ = l_Lake_captureProc_x3f(v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object* v_remote_772_, lean_object* v_repo_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_772_, v_repo_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object* v_remote_776_, lean_object* v_repo_777_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_776_, v_repo_777_);
if (lean_obj_tag(v___x_779_) == 0)
{
return v___x_779_;
}
else
{
lean_object* v_val_780_; lean_object* v___x_781_; 
v_val_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_val_780_);
lean_dec_ref(v___x_779_);
v___x_781_ = l_Lake_Git_filterUrl_x3f(v_val_780_);
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object* v_remote_782_, lean_object* v_repo_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v_remote_782_, v_repo_783_);
return v_res_785_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object* v_repo_796_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_798_ = ((lean_object*)(l_Lake_GitRepo_hasNoDiff___closed__2));
v___x_799_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_800_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_801_, 0, v_repo_796_);
v___x_802_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_803_ = 1;
v___x_804_ = 0;
v___x_805_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_805_, 0, v___x_799_);
lean_ctor_set(v___x_805_, 1, v___x_800_);
lean_ctor_set(v___x_805_, 2, v___x_798_);
lean_ctor_set(v___x_805_, 3, v___x_801_);
lean_ctor_set(v___x_805_, 4, v___x_802_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*5, v___x_803_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*5 + 1, v___x_804_);
v___x_806_ = l_Lake_testProc(v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object* v_repo_807_, lean_object* v_a_808_){
_start:
{
uint8_t v_res_809_; lean_object* v_r_810_; 
v_res_809_ = l_Lake_GitRepo_hasNoDiff(v_repo_807_);
v_r_810_ = lean_box(v_res_809_);
return v_r_810_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object* v_repo_811_){
_start:
{
uint8_t v___x_813_; 
v___x_813_ = l_Lake_GitRepo_hasNoDiff(v_repo_811_);
if (v___x_813_ == 0)
{
uint8_t v___x_814_; 
v___x_814_ = 1;
return v___x_814_;
}
else
{
uint8_t v___x_815_; 
v___x_815_ = 0;
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object* v_repo_816_, lean_object* v_a_817_){
_start:
{
uint8_t v_res_818_; lean_object* v_r_819_; 
v_res_818_ = l_Lake_GitRepo_hasDiff(v_repo_816_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Git(builtin);
}
#ifdef __cplusplus
}
#endif
