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
static const lean_string_object l_Lake_GitRepo_clean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clean"};
static const lean_object* l_Lake_GitRepo_clean___closed__0 = (const lean_object*)&l_Lake_GitRepo_clean___closed__0_value;
static const lean_string_object l_Lake_GitRepo_clean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-xf"};
static const lean_object* l_Lake_GitRepo_clean___closed__1 = (const lean_object*)&l_Lake_GitRepo_clean___closed__1_value;
static const lean_array_object l_Lake_GitRepo_clean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_clean___closed__0_value),((lean_object*)&l_Lake_GitRepo_clean___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_clean___closed__2 = (const lean_object*)&l_Lake_GitRepo_clean___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean(lean_object* v_repo_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_362_ = ((lean_object*)(l_Lake_GitRepo_clean___closed__2));
v___x_363_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_364_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v_repo_359_);
v___x_366_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_367_ = 1;
v___x_368_ = 0;
v___x_369_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_369_, 0, v___x_363_);
lean_ctor_set(v___x_369_, 1, v___x_364_);
lean_ctor_set(v___x_369_, 2, v___x_362_);
lean_ctor_set(v___x_369_, 3, v___x_365_);
lean_ctor_set(v___x_369_, 4, v___x_366_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*5, v___x_367_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*5 + 1, v___x_368_);
v___x_370_ = l_Lake_proc(v___x_369_, v___x_367_, v_a_360_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean___boxed(lean_object* v_repo_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lake_GitRepo_clean(v_repo_371_, v_a_372_);
return v_res_374_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_377_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_378_ = lean_unsigned_to_nat(4u);
v___x_379_ = lean_mk_empty_array_with_capacity(v___x_378_);
v___x_380_ = lean_array_push(v___x_379_, v___x_377_);
return v___x_380_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_382_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__2, &l_Lake_GitRepo_resolveRevision_x3f___closed__2_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2);
v___x_383_ = lean_array_push(v___x_382_, v___x_381_);
return v___x_383_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__1));
v___x_385_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__3, &l_Lake_GitRepo_resolveRevision_x3f___closed__3_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3);
v___x_386_ = lean_array_push(v___x_385_, v___x_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object* v_rev_387_, lean_object* v_repo_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; uint8_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_390_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__4, &l_Lake_GitRepo_resolveRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4);
v___x_391_ = lean_array_push(v___x_390_, v_rev_387_);
v___x_392_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_393_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v_repo_388_);
v___x_395_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_396_ = 1;
v___x_397_ = 0;
v___x_398_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_398_, 0, v___x_392_);
lean_ctor_set(v___x_398_, 1, v___x_393_);
lean_ctor_set(v___x_398_, 2, v___x_391_);
lean_ctor_set(v___x_398_, 3, v___x_394_);
lean_ctor_set(v___x_398_, 4, v___x_395_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*5, v___x_396_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*5 + 1, v___x_397_);
v___x_399_ = l_Lake_captureProc_x3f(v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object* v_rev_400_, lean_object* v_repo_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_400_, v_repo_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object* v_rev_406_, lean_object* v_repo_407_, lean_object* v_a_408_){
_start:
{
uint8_t v___x_410_; 
lean_inc_ref(v_rev_406_);
v___x_410_ = l_Lake_Git_isFullObjectName(v_rev_406_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_inc_ref(v_repo_407_);
lean_inc_ref(v_rev_406_);
v___x_411_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_406_, v_repo_407_);
if (lean_obj_tag(v___x_411_) == 1)
{
lean_object* v_val_412_; lean_object* v___x_413_; 
lean_dec_ref(v_repo_407_);
lean_dec_ref(v_rev_406_);
v_val_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_val_412_);
lean_dec_ref(v___x_411_);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v_val_412_);
lean_ctor_set(v___x_413_, 1, v_a_408_);
return v___x_413_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec(v___x_411_);
v___x_414_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_415_ = lean_string_append(v_repo_407_, v___x_414_);
v___x_416_ = lean_string_append(v___x_415_, v_rev_406_);
lean_dec_ref(v_rev_406_);
v___x_417_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_418_ = lean_string_append(v___x_416_, v___x_417_);
v___x_419_ = 3;
v___x_420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*1, v___x_419_);
v___x_421_ = lean_array_get_size(v_a_408_);
v___x_422_ = lean_array_push(v_a_408_, v___x_420_);
v___x_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
return v___x_423_;
}
}
else
{
lean_object* v___x_424_; 
lean_dec_ref(v_repo_407_);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v_rev_406_);
lean_ctor_set(v___x_424_, 1, v_a_408_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object* v_rev_425_, lean_object* v_repo_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lake_GitRepo_resolveRevision(v_rev_425_, v_repo_426_, v_a_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object* v_repo_431_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision_x3f___closed__0));
v___x_434_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_433_, v_repo_431_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object* v_repo_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lake_GitRepo_getHeadRevision_x3f(v_repo_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object* v_repo_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision_x3f___closed__0));
lean_inc_ref(v_repo_439_);
v___x_443_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_442_, v_repo_439_);
if (lean_obj_tag(v___x_443_) == 1)
{
lean_object* v_val_444_; lean_object* v___x_445_; 
lean_dec_ref(v_repo_439_);
v_val_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_val_444_);
lean_dec_ref(v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_val_444_);
lean_ctor_set(v___x_445_, 1, v_a_440_);
return v___x_445_;
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec(v___x_443_);
v___x_446_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision___closed__0));
v___x_447_ = lean_string_append(v_repo_439_, v___x_446_);
v___x_448_ = 3;
v___x_449_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*1, v___x_448_);
v___x_450_ = lean_array_get_size(v_a_440_);
v___x_451_ = lean_array_push(v_a_440_, v___x_449_);
v___x_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_450_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object* v_repo_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lake_GitRepo_getHeadRevision(v_repo_453_, v_a_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object* v_s_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0));
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object* v_s_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v_s_461_);
lean_dec_ref(v_s_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object* v___x_463_, lean_object* v___x_464_, lean_object* v___x_465_, lean_object* v_a_466_, lean_object* v_b_467_){
_start:
{
lean_object* v_it_469_; lean_object* v_startInclusive_470_; lean_object* v_endExclusive_471_; 
if (lean_obj_tag(v_a_466_) == 0)
{
lean_object* v_currPos_476_; lean_object* v_searcher_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_503_; 
v_currPos_476_ = lean_ctor_get(v_a_466_, 0);
v_searcher_477_ = lean_ctor_get(v_a_466_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v_a_466_);
if (v_isSharedCheck_503_ == 0)
{
v___x_479_ = v_a_466_;
v_isShared_480_ = v_isSharedCheck_503_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_searcher_477_);
lean_inc(v_currPos_476_);
lean_dec(v_a_466_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_503_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v_startInclusive_481_; lean_object* v_endExclusive_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_startInclusive_481_ = lean_ctor_get(v___x_464_, 1);
v_endExclusive_482_ = lean_ctor_get(v___x_464_, 2);
v___x_483_ = lean_nat_sub(v_endExclusive_482_, v_startInclusive_481_);
v___x_484_ = lean_nat_dec_eq(v_searcher_477_, v___x_483_);
lean_dec(v___x_483_);
if (v___x_484_ == 0)
{
uint32_t v___x_485_; uint32_t v___x_486_; uint8_t v___x_487_; 
v___x_485_ = 10;
v___x_486_ = lean_string_utf8_get_fast(v___x_463_, v_searcher_477_);
v___x_487_ = lean_uint32_dec_eq(v___x_486_, v___x_485_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_488_ = lean_string_utf8_next_fast(v___x_463_, v_searcher_477_);
lean_dec(v_searcher_477_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v___x_488_);
v___x_490_ = v___x_479_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_currPos_476_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_488_);
v___x_490_ = v_reuseFailAlloc_492_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
v_a_466_ = v___x_490_;
goto _start;
}
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_slice_496_; lean_object* v_nextIt_498_; 
v___x_493_ = lean_string_utf8_next_fast(v___x_463_, v_searcher_477_);
v___x_494_ = lean_nat_sub(v___x_493_, v_searcher_477_);
v___x_495_ = lean_nat_add(v_searcher_477_, v___x_494_);
lean_dec(v___x_494_);
v_slice_496_ = l_String_Slice_subslice_x21(v___x_464_, v_currPos_476_, v_searcher_477_);
lean_inc(v___x_495_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v___x_495_);
lean_ctor_set(v___x_479_, 0, v___x_495_);
v_nextIt_498_ = v___x_479_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v___x_495_);
v_nextIt_498_ = v_reuseFailAlloc_501_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v_startInclusive_499_; lean_object* v_endExclusive_500_; 
v_startInclusive_499_ = lean_ctor_get(v_slice_496_, 0);
lean_inc(v_startInclusive_499_);
v_endExclusive_500_ = lean_ctor_get(v_slice_496_, 1);
lean_inc(v_endExclusive_500_);
lean_dec_ref(v_slice_496_);
v_it_469_ = v_nextIt_498_;
v_startInclusive_470_ = v_startInclusive_499_;
v_endExclusive_471_ = v_endExclusive_500_;
goto v___jp_468_;
}
}
}
else
{
lean_object* v___x_502_; 
lean_del_object(v___x_479_);
lean_dec(v_searcher_477_);
v___x_502_ = lean_box(1);
lean_inc(v___x_465_);
v_it_469_ = v___x_502_;
v_startInclusive_470_ = v_currPos_476_;
v_endExclusive_471_ = v___x_465_;
goto v___jp_468_;
}
}
}
else
{
lean_dec(v___x_465_);
lean_dec_ref(v___x_463_);
return v_b_467_;
}
v___jp_468_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
lean_inc_ref(v___x_463_);
v___x_472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_472_, 0, v___x_463_);
lean_ctor_set(v___x_472_, 1, v_startInclusive_470_);
lean_ctor_set(v___x_472_, 2, v_endExclusive_471_);
v___x_473_ = l_String_Slice_toString(v___x_472_);
lean_dec_ref(v___x_472_);
v___x_474_ = lean_array_push(v_b_467_, v___x_473_);
v_a_466_ = v_it_469_;
v_b_467_ = v___x_474_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object* v___x_504_, lean_object* v___x_505_, lean_object* v___x_506_, lean_object* v_a_507_, lean_object* v_b_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_504_, v___x_505_, v___x_506_, v_a_507_, v_b_508_);
lean_dec_ref(v___x_505_);
return v_res_509_;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevisions___closed__3(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_518_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__2));
v___x_519_ = lean_unsigned_to_nat(2u);
v___x_520_ = lean_mk_empty_array_with_capacity(v___x_519_);
v___x_521_ = lean_array_push(v___x_520_, v___x_518_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object* v_repo_522_, lean_object* v_n_523_, lean_object* v_a_524_){
_start:
{
lean_object* v___y_527_; lean_object* v_args_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_args_573_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__1));
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_nat_dec_eq(v_n_523_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_576_ = l_Nat_reprFast(v_n_523_);
v___x_577_ = lean_obj_once(&l_Lake_GitRepo_getHeadRevisions___closed__3, &l_Lake_GitRepo_getHeadRevisions___closed__3_once, _init_l_Lake_GitRepo_getHeadRevisions___closed__3);
v___x_578_ = lean_array_push(v___x_577_, v___x_576_);
v___x_579_ = l_Array_append___redArg(v_args_573_, v___x_578_);
lean_dec_ref(v___x_578_);
v___y_527_ = v___x_579_;
goto v___jp_526_;
}
else
{
lean_dec(v_n_523_);
v___y_527_ = v_args_573_;
goto v___jp_526_;
}
v___jp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; uint8_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_528_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_529_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v_repo_522_);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_533_ = 1;
v___x_534_ = 0;
v___x_535_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_535_, 0, v___x_528_);
lean_ctor_set(v___x_535_, 1, v___x_529_);
lean_ctor_set(v___x_535_, 2, v___y_527_);
lean_ctor_set(v___x_535_, 3, v___x_530_);
lean_ctor_set(v___x_535_, 4, v___x_532_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*5, v___x_533_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*5 + 1, v___x_534_);
v___x_536_ = l_Lake_captureProc_x27(v___x_535_, v_a_524_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_563_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
v_a_538_ = lean_ctor_get(v___x_536_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_563_ == 0)
{
v___x_540_ = v___x_536_;
v_isShared_541_ = v_isSharedCheck_563_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_inc(v_a_537_);
lean_dec(v___x_536_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_563_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_stdout_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v_str_546_; lean_object* v_startInclusive_547_; lean_object* v_endExclusive_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_562_; 
v_stdout_542_ = lean_ctor_get(v_a_537_, 0);
lean_inc_ref(v_stdout_542_);
lean_dec(v_a_537_);
v___x_543_ = lean_string_utf8_byte_size(v_stdout_542_);
v___x_544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_544_, 0, v_stdout_542_);
lean_ctor_set(v___x_544_, 1, v___x_531_);
lean_ctor_set(v___x_544_, 2, v___x_543_);
v___x_545_ = l_String_Slice_trimAscii(v___x_544_);
v_str_546_ = lean_ctor_get(v___x_545_, 0);
v_startInclusive_547_ = lean_ctor_get(v___x_545_, 1);
v_endExclusive_548_ = lean_ctor_get(v___x_545_, 2);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_562_ == 0)
{
v___x_550_ = v___x_545_;
v_isShared_551_ = v_isSharedCheck_562_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_endExclusive_548_);
lean_inc(v_startInclusive_547_);
lean_inc(v_str_546_);
lean_dec(v___x_545_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_562_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_552_ = lean_string_utf8_extract(v_str_546_, v_startInclusive_547_, v_endExclusive_548_);
lean_dec(v_endExclusive_548_);
lean_dec(v_startInclusive_547_);
lean_dec_ref(v_str_546_);
v___x_553_ = lean_string_utf8_byte_size(v___x_552_);
lean_inc_ref(v___x_552_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 2, v___x_553_);
lean_ctor_set(v___x_550_, 1, v___x_531_);
lean_ctor_set(v___x_550_, 0, v___x_552_);
v___x_555_ = v___x_550_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v___x_553_);
v___x_555_ = v_reuseFailAlloc_561_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v___x_555_);
v___x_557_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_552_, v___x_555_, v___x_553_, v___x_556_, v___x_532_);
lean_dec_ref(v___x_555_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_557_);
v___x_559_ = v___x_540_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_a_538_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
v_a_564_ = lean_ctor_get(v___x_536_, 0);
v_a_565_ = lean_ctor_get(v___x_536_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_536_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_inc(v_a_564_);
lean_dec(v___x_536_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_564_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object* v_repo_580_, lean_object* v_n_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lake_GitRepo_getHeadRevisions(v_repo_580_, v_n_581_, v_a_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object* v___x_585_, lean_object* v___x_586_, lean_object* v___x_587_, lean_object* v_inst_588_, lean_object* v_R_589_, lean_object* v_a_590_, lean_object* v_b_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_585_, v___x_586_, v___x_587_, v_a_590_, v_b_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object* v___x_593_, lean_object* v___x_594_, lean_object* v___x_595_, lean_object* v_inst_596_, lean_object* v_R_597_, lean_object* v_a_598_, lean_object* v_b_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(v___x_593_, v___x_594_, v___x_595_, v_inst_596_, v_R_597_, v_a_598_, v_b_599_);
lean_dec_ref(v___x_594_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object* v_rev_602_, lean_object* v_remote_603_, lean_object* v_repo_604_, lean_object* v_a_605_){
_start:
{
uint8_t v___x_607_; 
lean_inc_ref(v_rev_602_);
v___x_607_ = l_Lake_Git_isFullObjectName(v_rev_602_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_608_ = ((lean_object*)(l_Lake_GitRepo_resolveRemoteRevision___closed__0));
v___x_609_ = lean_string_append(v_remote_603_, v___x_608_);
v___x_610_ = lean_string_append(v___x_609_, v_rev_602_);
lean_inc_ref(v_repo_604_);
v___x_611_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_610_, v_repo_604_);
if (lean_obj_tag(v___x_611_) == 1)
{
lean_object* v_val_612_; lean_object* v___x_613_; 
lean_dec_ref(v_repo_604_);
lean_dec_ref(v_rev_602_);
v_val_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_val_612_);
lean_dec_ref(v___x_611_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v_val_612_);
lean_ctor_set(v___x_613_, 1, v_a_605_);
return v___x_613_;
}
else
{
lean_object* v___x_614_; 
lean_dec(v___x_611_);
lean_inc_ref(v_repo_604_);
lean_inc_ref(v_rev_602_);
v___x_614_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_602_, v_repo_604_);
if (lean_obj_tag(v___x_614_) == 1)
{
lean_object* v_val_615_; lean_object* v___x_616_; 
lean_dec_ref(v_repo_604_);
lean_dec_ref(v_rev_602_);
v_val_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_val_615_);
lean_dec_ref(v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v_val_615_);
lean_ctor_set(v___x_616_, 1, v_a_605_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v___x_614_);
v___x_617_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_618_ = lean_string_append(v_repo_604_, v___x_617_);
v___x_619_ = lean_string_append(v___x_618_, v_rev_602_);
lean_dec_ref(v_rev_602_);
v___x_620_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_621_ = lean_string_append(v___x_619_, v___x_620_);
v___x_622_ = 3;
v___x_623_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*1, v___x_622_);
v___x_624_ = lean_array_get_size(v_a_605_);
v___x_625_ = lean_array_push(v_a_605_, v___x_623_);
v___x_626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
return v___x_626_;
}
}
}
else
{
lean_object* v___x_627_; 
lean_dec_ref(v_repo_604_);
lean_dec_ref(v_remote_603_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v_rev_602_);
lean_ctor_set(v___x_627_, 1, v_a_605_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object* v_rev_628_, lean_object* v_remote_629_, lean_object* v_repo_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lake_GitRepo_resolveRemoteRevision(v_rev_628_, v_remote_629_, v_repo_630_, v_a_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object* v_repo_634_, lean_object* v_rev_x3f_635_, lean_object* v_remote_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___x_639_; 
lean_inc_ref(v_remote_636_);
lean_inc_ref(v_repo_634_);
v___x_639_ = l_Lake_GitRepo_fetch(v_repo_634_, v_remote_636_, v_a_637_);
if (lean_obj_tag(v___x_639_) == 0)
{
if (lean_obj_tag(v_rev_x3f_635_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_a_640_ = lean_ctor_get(v___x_639_, 1);
lean_inc(v_a_640_);
lean_dec_ref(v___x_639_);
v___x_641_ = ((lean_object*)(l_Lake_Git_upstreamBranch___closed__0));
v___x_642_ = l_Lake_GitRepo_resolveRemoteRevision(v___x_641_, v_remote_636_, v_repo_634_, v_a_640_);
return v___x_642_;
}
else
{
lean_object* v_a_643_; lean_object* v_val_644_; lean_object* v___x_645_; 
v_a_643_ = lean_ctor_get(v___x_639_, 1);
lean_inc(v_a_643_);
lean_dec_ref(v___x_639_);
v_val_644_ = lean_ctor_get(v_rev_x3f_635_, 0);
lean_inc(v_val_644_);
lean_dec_ref(v_rev_x3f_635_);
v___x_645_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_644_, v_remote_636_, v_repo_634_, v_a_643_);
return v___x_645_;
}
}
else
{
lean_object* v_a_646_; lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec_ref(v_remote_636_);
lean_dec(v_rev_x3f_635_);
lean_dec_ref(v_repo_634_);
v_a_646_ = lean_ctor_get(v___x_639_, 0);
v_a_647_ = lean_ctor_get(v___x_639_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_639_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_inc(v_a_646_);
lean_dec(v___x_639_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_646_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object* v_repo_655_, lean_object* v_rev_x3f_656_, lean_object* v_remote_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lake_GitRepo_findRemoteRevision(v_repo_655_, v_rev_x3f_656_, v_remote_657_, v_a_658_);
return v_res_660_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__2(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_663_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__0));
v___x_664_ = lean_unsigned_to_nat(3u);
v___x_665_ = lean_mk_empty_array_with_capacity(v___x_664_);
v___x_666_ = lean_array_push(v___x_665_, v___x_663_);
return v___x_666_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__3(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_668_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__2, &l_Lake_GitRepo_branchExists___closed__2_once, _init_l_Lake_GitRepo_branchExists___closed__2);
v___x_669_ = lean_array_push(v___x_668_, v___x_667_);
return v___x_669_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object* v_rev_670_, lean_object* v_repo_671_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; uint8_t v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_673_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__1));
v___x_674_ = lean_string_append(v___x_673_, v_rev_670_);
v___x_675_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__3, &l_Lake_GitRepo_branchExists___closed__3_once, _init_l_Lake_GitRepo_branchExists___closed__3);
v___x_676_ = lean_array_push(v___x_675_, v___x_674_);
v___x_677_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_678_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v_repo_671_);
v___x_680_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_681_ = 1;
v___x_682_ = 0;
v___x_683_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_683_, 0, v___x_677_);
lean_ctor_set(v___x_683_, 1, v___x_678_);
lean_ctor_set(v___x_683_, 2, v___x_676_);
lean_ctor_set(v___x_683_, 3, v___x_679_);
lean_ctor_set(v___x_683_, 4, v___x_680_);
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*5, v___x_681_);
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*5 + 1, v___x_682_);
v___x_684_ = l_Lake_testProc(v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object* v_rev_685_, lean_object* v_repo_686_, lean_object* v_a_687_){
_start:
{
uint8_t v_res_688_; lean_object* v_r_689_; 
v_res_688_ = l_Lake_GitRepo_branchExists(v_rev_685_, v_repo_686_);
lean_dec_ref(v_rev_685_);
v_r_689_ = lean_box(v_res_688_);
return v_r_689_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__1(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_691_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_692_ = lean_unsigned_to_nat(3u);
v___x_693_ = lean_mk_empty_array_with_capacity(v___x_692_);
v___x_694_ = lean_array_push(v___x_693_, v___x_691_);
return v___x_694_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__2(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_696_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__1, &l_Lake_GitRepo_revisionExists___closed__1_once, _init_l_Lake_GitRepo_revisionExists___closed__1);
v___x_697_ = lean_array_push(v___x_696_, v___x_695_);
return v___x_697_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object* v_rev_698_, lean_object* v_repo_699_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; uint8_t v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_701_ = ((lean_object*)(l_Lake_GitRepo_revisionExists___closed__0));
v___x_702_ = lean_string_append(v_rev_698_, v___x_701_);
v___x_703_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__2, &l_Lake_GitRepo_revisionExists___closed__2_once, _init_l_Lake_GitRepo_revisionExists___closed__2);
v___x_704_ = lean_array_push(v___x_703_, v___x_702_);
v___x_705_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_706_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_707_, 0, v_repo_699_);
v___x_708_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_709_ = 1;
v___x_710_ = 0;
v___x_711_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_711_, 0, v___x_705_);
lean_ctor_set(v___x_711_, 1, v___x_706_);
lean_ctor_set(v___x_711_, 2, v___x_704_);
lean_ctor_set(v___x_711_, 3, v___x_707_);
lean_ctor_set(v___x_711_, 4, v___x_708_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*5, v___x_709_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*5 + 1, v___x_710_);
v___x_712_ = l_Lake_testProc(v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object* v_rev_713_, lean_object* v_repo_714_, lean_object* v_a_715_){
_start:
{
uint8_t v_res_716_; lean_object* v_r_717_; 
v_res_716_ = l_Lake_GitRepo_revisionExists(v_rev_713_, v_repo_714_);
v_r_717_ = lean_box(v_res_716_);
return v_r_717_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object* v_repo_723_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_725_ = ((lean_object*)(l_Lake_GitRepo_getTags___closed__1));
v___x_726_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_727_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_repo_723_);
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_731_ = 1;
v___x_732_ = 0;
v___x_733_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_733_, 0, v___x_726_);
lean_ctor_set(v___x_733_, 1, v___x_727_);
lean_ctor_set(v___x_733_, 2, v___x_725_);
lean_ctor_set(v___x_733_, 3, v___x_728_);
lean_ctor_set(v___x_733_, 4, v___x_730_);
lean_ctor_set_uint8(v___x_733_, sizeof(void*)*5, v___x_731_);
lean_ctor_set_uint8(v___x_733_, sizeof(void*)*5 + 1, v___x_732_);
v___x_734_ = l_Lake_captureProc_x3f(v___x_733_);
if (lean_obj_tag(v___x_734_) == 1)
{
lean_object* v_val_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_val_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc_n(v_val_735_, 2);
lean_dec_ref(v___x_734_);
v___x_736_ = lean_string_utf8_byte_size(v_val_735_);
v___x_737_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_737_, 0, v_val_735_);
lean_ctor_set(v___x_737_, 1, v___x_729_);
lean_ctor_set(v___x_737_, 2, v___x_736_);
v___x_738_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v___x_737_);
v___x_739_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v_val_735_, v___x_737_, v___x_736_, v___x_738_, v___x_730_);
lean_dec_ref(v___x_737_);
v___x_740_ = lean_array_to_list(v___x_739_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; 
lean_dec(v___x_734_);
v___x_741_ = lean_box(0);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object* v_repo_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lake_GitRepo_getTags(v_repo_742_);
return v_res_744_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__2(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_747_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__0));
v___x_748_ = lean_unsigned_to_nat(4u);
v___x_749_ = lean_mk_empty_array_with_capacity(v___x_748_);
v___x_750_ = lean_array_push(v___x_749_, v___x_747_);
return v___x_750_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__3(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_752_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__2, &l_Lake_GitRepo_findTag_x3f___closed__2_once, _init_l_Lake_GitRepo_findTag_x3f___closed__2);
v___x_753_ = lean_array_push(v___x_752_, v___x_751_);
return v___x_753_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__4(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__1));
v___x_755_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__3, &l_Lake_GitRepo_findTag_x3f___closed__3_once, _init_l_Lake_GitRepo_findTag_x3f___closed__3);
v___x_756_ = lean_array_push(v___x_755_, v___x_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object* v_rev_757_, lean_object* v_repo_758_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_760_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__4, &l_Lake_GitRepo_findTag_x3f___closed__4_once, _init_l_Lake_GitRepo_findTag_x3f___closed__4);
v___x_761_ = lean_array_push(v___x_760_, v_rev_757_);
v___x_762_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_763_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_764_, 0, v_repo_758_);
v___x_765_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_766_ = 1;
v___x_767_ = 0;
v___x_768_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_768_, 0, v___x_762_);
lean_ctor_set(v___x_768_, 1, v___x_763_);
lean_ctor_set(v___x_768_, 2, v___x_761_);
lean_ctor_set(v___x_768_, 3, v___x_764_);
lean_ctor_set(v___x_768_, 4, v___x_765_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*5, v___x_766_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*5 + 1, v___x_767_);
v___x_769_ = l_Lake_captureProc_x3f(v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object* v_rev_770_, lean_object* v_repo_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lake_GitRepo_findTag_x3f(v_rev_770_, v_repo_771_);
return v_res_773_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_776_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
v___x_777_ = lean_unsigned_to_nat(3u);
v___x_778_ = lean_mk_empty_array_with_capacity(v___x_777_);
v___x_779_ = lean_array_push(v___x_778_, v___x_776_);
return v___x_779_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__1));
v___x_781_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__2, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
v___x_782_ = lean_array_push(v___x_781_, v___x_780_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object* v_remote_783_, lean_object* v_repo_784_){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; uint8_t v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_786_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__3, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3);
v___x_787_ = lean_array_push(v___x_786_, v_remote_783_);
v___x_788_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_789_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_790_, 0, v_repo_784_);
v___x_791_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_792_ = 1;
v___x_793_ = 0;
v___x_794_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_794_, 0, v___x_788_);
lean_ctor_set(v___x_794_, 1, v___x_789_);
lean_ctor_set(v___x_794_, 2, v___x_787_);
lean_ctor_set(v___x_794_, 3, v___x_790_);
lean_ctor_set(v___x_794_, 4, v___x_791_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*5, v___x_792_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*5 + 1, v___x_793_);
v___x_795_ = l_Lake_captureProc_x3f(v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object* v_remote_796_, lean_object* v_repo_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_796_, v_repo_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object* v_remote_800_, lean_object* v_repo_801_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_800_, v_repo_801_);
if (lean_obj_tag(v___x_803_) == 0)
{
return v___x_803_;
}
else
{
lean_object* v_val_804_; lean_object* v___x_805_; 
v_val_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_val_804_);
lean_dec_ref(v___x_803_);
v___x_805_ = l_Lake_Git_filterUrl_x3f(v_val_804_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object* v_remote_806_, lean_object* v_repo_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v_remote_806_, v_repo_807_);
return v_res_809_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object* v_repo_820_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; uint8_t v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_822_ = ((lean_object*)(l_Lake_GitRepo_hasNoDiff___closed__2));
v___x_823_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_824_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_825_, 0, v_repo_820_);
v___x_826_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_827_ = 1;
v___x_828_ = 0;
v___x_829_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_829_, 0, v___x_823_);
lean_ctor_set(v___x_829_, 1, v___x_824_);
lean_ctor_set(v___x_829_, 2, v___x_822_);
lean_ctor_set(v___x_829_, 3, v___x_825_);
lean_ctor_set(v___x_829_, 4, v___x_826_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*5, v___x_827_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*5 + 1, v___x_828_);
v___x_830_ = l_Lake_testProc(v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object* v_repo_831_, lean_object* v_a_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_Lake_GitRepo_hasNoDiff(v_repo_831_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object* v_repo_835_){
_start:
{
uint8_t v___x_837_; 
v___x_837_ = l_Lake_GitRepo_hasNoDiff(v_repo_835_);
if (v___x_837_ == 0)
{
uint8_t v___x_838_; 
v___x_838_ = 1;
return v___x_838_;
}
else
{
uint8_t v___x_839_; 
v___x_839_ = 0;
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object* v_repo_840_, lean_object* v_a_841_){
_start:
{
uint8_t v_res_842_; lean_object* v_r_843_; 
v_res_842_ = l_Lake_GitRepo_hasDiff(v_repo_840_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
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
