interface Dict<V> {
  [key: string]: V;
}

export class Dictionary<V> {
  private _d: Dict<V> = {};
  public contains(key: string): boolean {
    return this._d[key] !== undefined;
  }
  public get(key: string): V {
    if (this.contains(key)) {
      return this._d[key];
    } else {
      throw new Error("Cannot get unknown key '" + key + "' in dictionary.");
    }
  }
  public put(key: string, value: V): void {
    this._d[key] = value;
  }
  public del(key: string): V {
    if (this.contains(key)) {
      const v = this._d[key];
      delete this._d[key];
      return v;
    } else {
      throw new Error("Cannot delete unknown key '" + key + "' in dictionary.");
    }
  }
  public get keys(): string[] {
    const output: string[] = [];
    for (let key in this._d) {
      output.push(key);
    }
    return output;
  }
  public get values(): V[] {
    const output: V[] = [];
    for (let key in this._d) {
      output.push(this._d[key]);
    }
    return output;
  }

  /**
   * Performs a shallow copy of the dictionary.
   */
  public clone(): Dictionary<V> {
    const dict = new Dictionary<V>();
    for (const key of this.keys) {
      dict.put(key, this.get(key));
    }
    return dict;
  }

  /**
   * Merges this dictionary with another dictionary.  Throws an exception if there are
   * duplicate keys. Returns a copy.
   * @param o The other dictionary.
   */
  public merge(o: Dictionary<V>): Dictionary<V> {
    const merged = this.clone();
    for (const key of o.keys) {
      if (merged.contains(key)) {
        throw new Error(
          "Cannot merge dictionaries that contain copies of the same key."
        );
      }
      merged.put(key, o.get(key));
    }
    return merged;
  }
}
