import sys
from setuptools import setup


if sys.version_info < (3, 0):
    sys.stderr.write("Sorry, Python < 3.0 is not supported\n")
    sys.exit(1)


setup(name='python-compiler',
      version='1.0',
      description="""Python bytecode compiler written in Python""",
      long_description=open('README.md').read(),
      long_description_content_type='text/markdown',
      url='https://github.com/pfalcon/python-compiler',
      author='Python Developers',
      maintainer='Paul Sokolovsky',
      maintainer_email='pfalcon@users.sourceforge.net',
      license='Python',
      packages=['compiler'])
