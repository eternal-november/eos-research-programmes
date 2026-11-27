"""Local, cooperative scheduler entitlement. This is not plant authority."""
from contextlib import closing
import sqlite3

class Gate:
    def __init__(self,path,cut):
        self.path=path
        self.cut=cut
        with closing(self.open()) as db:
            db.executescript("""create table stage (
              cut text primary key, owner text, used integer not null
            )""")
            db.execute("insert into stage values (?,NULL,0)",(cut,))
    def open(self):
        return sqlite3.connect(self.path,isolation_level=None)
    def show(self):
        with closing(self.open()) as db:
            return db.execute("select owner,used from stage where cut=?",(self.cut,)).fetchone()
    def claim(self,who):
        with closing(self.open()) as db:
            db.execute("begin immediate")
            go=db.execute("update stage set owner=? where cut=? and owner is null and used=0",
                          (who,self.cut)).rowcount==1
            db.execute("commit")
        return (self.cut,who) if go else None
    def consume(self,key):
        assert key is not None
        cut,who=key
        with closing(self.open()) as db:
            db.execute("begin immediate")
            go=db.execute("update stage set used=1 where cut=? and owner=? and used=0",
                          (cut,who)).rowcount==1
            db.execute("commit")
        return go
