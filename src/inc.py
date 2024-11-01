#!venv/bin/python3
import pymysql
from contextlib import closing

def increment(key, cursor):
    cursor.execute("SELECT v FROM obj WHERE k = %s", (key, ))
    val = cursor.fetchone()[0]
    cursor.execute("UPDATE obj SET v=%s WHERE k = %s", (val+1, key))

with closing(pymysql.connect(user="root", database="tla")) as c:
    c.begin()
    with closing(c.cursor()) as cursor: 
        inc("x", cursor)
    c.commit()
