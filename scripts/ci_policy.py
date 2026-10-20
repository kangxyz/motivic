# Authors: kangxyz
"""Exact hosted producer identities; approval requires actual source review.

This policy stays outside its own recipe tuple. Supporting-source correctness
is an owner-reviewed trusted-producer premise, not a consequence of hashing.
No legacy Motivic smoke run is admitted as a complete native baseline.
"""
from lean_ci.github import EvidenceProtocol

TOOLING_REVISION = '0caa3a890c9cbeb7ade5e4f804203b31b5b0b3b1'
CORE_ENTRYPOINTS = {
    'scripts/build.py': '2c982b802bc7b5a0dcb0d74de4e8ea39abbe0b41f1838757e1a7685f71de43c5',
    'scripts/build_client.py': 'c47886425b6b0dc0f341695dbd42e838f94434c9e0c626acfb3405632b937e9c',
    'scripts/build_modules.py': '4a173dc2692df9ebb164bbbc50e870c072e4fda3f9fd4e71eba72d15e80bf880',
    'scripts/cache.py': '5fa4770e339e06d5082f9e8a6dc80f78d8c22c681462984bd850dbf529a4bd9d',
    'scripts/cache_bootstrap.py': '8fd6212e06f233b03330c6d5fe81b47befe63b4795d79cd536c5bf17dc4b5613',
    'scripts/check_repository.py': 'bcf2f69052c1d7c93fbda0405879a2d77c06b2826d9ff0af8eb490fce177292c',
    'scripts/ci_targets.py': '898a5ecd53aa9b32684e7846ef7e2c9030ebbdf74bb727aea92e472b232c1cf2',
    'scripts/generate_imports.py': '03244f02a590b60c7aa584eeddceb7f74ddd950e945b7f0b27b248fd4820be41',
    'scripts/library_sources.py': '1fe323386e801d2bb9c8d3fa1f64fce4564f00dac6e5392f241a5424d8cf8369',
    'scripts/lint_declarations.py': '6013e20c073904e077ad27c1e17d651e95d9c2c00db0dd3af6c9a35d15f5ed2b',
    'scripts/lint_style.py': '1733a915dddfaf185702dd250568bd63b88cb4a4b0f95d9e6f1a43a028cd522e',
    'scripts/shared_workflow.py': '731b1c8ce21a31e467d9a896fcfb3ed510c7635081207eb36e596557dc97945d',
    'scripts/validate.py': 'efc5e29da391aadf95ee168e4491949224b9bc344895d9831222fa0d91f0d05f',
}
PROTOCOL = EvidenceProtocol(
    workflow_path='.github/workflows/ci.yml', job_name='library',
    native_step='Validate selected providers before affected consumers and client',
    finalize_step='Finalize required check coverage',
    workflows={'239a524b2a18e4fbda6a5629f4106d9c0cdc28578bc6b0ea59f91fce59767f6a': 'core'},
    core_entrypoint_paths=tuple(CORE_ENTRYPOINTS),
    core_recipes=frozenset({tuple(CORE_ENTRYPOINTS.values())}))
